import ComplexityOfGenerators.Foundations.FixedBlockSelection

/-! A finite observed prefix and the unread suffix of the actual fair stream
have the product law. Retry stopping times are treated by their measurable
first-success partition, so fresh calls need no independence premise. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

private abbrev PrefixTailIndex (width : ℕ) (which : Fin 2) : Type :=
  if which.val = 0 then Fin width else ℕ

private def prefixTailOffset (width : ℕ) (which : Fin 2) : PrefixTailIndex width which → ℕ :=
  if h : which.val = 0 then fun i => (cast (by simp [PrefixTailIndex, h]) i : Fin width).val
  else fun i => width + (cast (by simp [PrefixTailIndex, h]) i : ℕ)

private def prefixTailIndexEquiv (width : ℕ) : (Σ which : Fin 2, PrefixTailIndex width which) ≃ ℕ where
  toFun position := prefixTailOffset width position.1 position.2
  invFun i := if h : i < width then ⟨0, ⟨i, h⟩⟩ else ⟨1, i - width⟩
  left_inv := by
    rintro ⟨which, i⟩
    fin_cases which
    · simp [prefixTailOffset, PrefixTailIndex, i.isLt]
    · simp [prefixTailOffset, PrefixTailIndex]
  right_inv := by
    intro i
    by_cases h : i < width
    · dsimp only
      rw [dite_eq_left h]
      simp [prefixTailOffset, PrefixTailIndex]
    · dsimp only
      rw [dite_eq_right h]
      simp [prefixTailOffset, PrefixTailIndex, Nat.add_sub_cancel' (Nat.le_of_not_gt h)]

def splitStream (width : ℕ) (stream : BitStream) : (Fin width → Bool) × BitStream :=
  (fun i => stream i.val, fun i => stream (width + i))

theorem measurable_splitStream (width : ℕ) : Measurable (splitStream width) := by
  apply Measurable.prodMk <;> apply Measurable.of_eval <;> intro i <;> exact measurable_pi_apply _

/-- The uninspected suffix is a new fair stream, independent of every bit in
the inspected finite prefix, including at width zero. -/
theorem fairCoinMeasure_map_splitStream (width : ℕ) :
    fairCoinMeasure.map (splitStream width) = (fairBlockMeasure width).prod fairCoinMeasure := by
  let e := prefixTailIndexEquiv width
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : Σ which : Fin 2, PrefixTailIndex width which => Bool) e.symm
  let curry := MeasurableEquiv.piCurry (fun (which : Fin 2) (_ : PrefixTailIndex width which) => Bool)
  let pair := MeasurableEquiv.piFinTwo (fun which : Fin 2 => PrefixTailIndex width which → Bool)
  have reindexLaw : fairCoinMeasure.map reindex =
      Measure.infinitePi (fun _ : Σ which : Fin 2, PrefixTailIndex width which =>
        (PMF.uniformOfFintype Bool).toMeasure) := by
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Σ which : Fin 2, PrefixTailIndex width which => (PMF.uniformOfFintype Bool).toMeasure) e.symm
  have curryLaw := Measure.infinitePi_map_piCurry
    (fun (which : Fin 2) (_ : PrefixTailIndex width which) => (PMF.uniformOfFintype Bool).toMeasure)
  have pairLaw := (measurePreserving_piFinTwo
    (fun which : Fin 2 => Measure.infinitePi
      (fun _ : PrefixTailIndex width which => (PMF.uniformOfFintype Bool).toMeasure))).map_eq
  have same : pair ∘ curry ∘ reindex = splitStream width := by
    funext stream
    apply Prod.ext <;> funext i
    · simp [pair, curry, reindex, e, prefixTailIndexEquiv, prefixTailOffset,
        MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.piFinTwo, Sigma.curry, Equiv.piCongrLeft, splitStream, Function.comp_def]
    · simp [pair, curry, reindex, e, prefixTailIndexEquiv, prefixTailOffset,
        MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.piFinTwo, Sigma.curry, Equiv.piCongrLeft, splitStream, Function.comp_def]
  have law : (fairCoinMeasure.map reindex |>.map curry |>.map pair) =
      (fairBlockMeasure width).prod fairCoinMeasure := by
    rw [reindexLaw, curryLaw, Measure.infinitePi_eq_pi]
    exact pairLaw
  rw [Measure.map_map curry.measurable reindex.measurable,
    Measure.map_map pair.measurable (curry.measurable.comp reindex.measurable)] at law
  simpa only [same] using law

/-- Arbitrary events in the observed prefix and unread suffix factor. -/
theorem fairCoinMeasure_prefix_tail (width : ℕ) (event : Set (Fin width → Bool))
    (future : Set BitStream) (eventMeasurable : MeasurableSet event) (futureMeasurable : MeasurableSet future) :
    fairCoinMeasure {stream | (splitStream width stream).1 ∈ event ∧
      (splitStream width stream).2 ∈ future} = fairBlockMeasure width event * fairCoinMeasure future := by
  have mapped := congrArg (fun μ : Measure ((Fin width → Bool) × BitStream) => μ (event ×ˢ future))
    (fairCoinMeasure_map_splitStream width)
  rw [Measure.map_apply (measurable_splitStream width) (eventMeasurable.prod futureMeasurable),
    Measure.prod_prod] at mapped
  exact mapped

end ComplexityOfGenerators

namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal

/-- Extend a finite random prefix by zeroes; this is used only to express
which events depend on that prefix. -/
def prefixExtension (width : ℕ) (bits : Fin width → Bool) : BitStream :=
  fun i => if h : i < width then bits ⟨i, h⟩ else false

theorem splitStream_prefixExtension (width : ℕ) (bits : Fin width → Bool) :
    (splitStream width (prefixExtension width bits)).1 = bits := by
  funext i
  simp [splitStream, prefixExtension, i.isLt]

/-- Any event determined by the inspected prefix is independent of the
unread suffix, with no requirement that the event be a single cylinder. -/
theorem fairCoinMeasure_prefix_event_tail (width : ℕ) (event future : Set BitStream)
    (determined : ∀ left right, (splitStream width left).1 = (splitStream width right).1 →
      (left ∈ event ↔ right ∈ event))
    (futureMeasurable : MeasurableSet future) :
    fairCoinMeasure (event ∩ {stream | (splitStream width stream).2 ∈ future}) =
      fairCoinMeasure event * fairCoinMeasure future := by
  let finiteEvent : Set (Fin width → Bool) := {bits | prefixExtension width bits ∈ event}
  have finiteMeasurable : MeasurableSet finiteEvent := Set.to_countable _ |>.measurableSet
  have describe : event = {stream | (splitStream width stream).1 ∈ finiteEvent} := by
    ext stream
    exact determined stream (prefixExtension width (splitStream width stream).1)
      (by rw [splitStream_prefixExtension])
  have mass := fairCoinMeasure_prefix_tail width finiteEvent Set.univ finiteMeasurable MeasurableSet.univ
  simp only [Set.mem_univ, and_true, measure_univ, mul_one] at mass
  rw [describe]
  exact (fairCoinMeasure_prefix_tail width finiteEvent future finiteMeasurable futureMeasurable).trans
    (congrArg (fun q : ℝ≥0∞ => q * fairCoinMeasure future) mass.symm)

/-- The first-success event up to attempt n inspects only (n+1) complete
blocks. It is therefore independent of any subsequent random computation. -/
theorem fairCoinMeasure_retryHit_tail (width n : ℕ) (success target : Set (Fin width → Bool))
    (future : Set BitStream) (futureMeasurable : MeasurableSet future) :
    fairCoinMeasure (retryHit width success target n ∩
      {stream | (splitStream ((n+1)*width) stream).2 ∈ future}) =
      fairCoinMeasure (retryHit width success target n) * fairCoinMeasure future := by
  apply fairCoinMeasure_prefix_event_tail _ _ _ _ futureMeasurable
  intro left right equal
  have blockEqual (j : ℕ) (bound : j ≤ n) : fixedBlock width left j = fixedBlock width right j := by
    funext offset
    have within : j*width + offset.val < (n+1)*width := by
      have := offset.isLt
      nlinarith
    exact congrFun equal ⟨j*width + offset.val, within⟩
  change ((∀ j < n, fixedBlock width left j ∉ success) ∧ fixedBlock width left n ∈ target) ↔ _
  constructor
  · rintro ⟨failed, hit⟩
    refine ⟨fun j earlier => ?_, ?_⟩
    · rw [← blockEqual j (by omega)]
      exact failed j earlier
    · change fixedBlock width right n ∈ target
      rw [← blockEqual n le_rfl]
      exact hit
  · rintro ⟨failed, hit⟩
    refine ⟨fun j earlier => ?_, ?_⟩
    · rw [blockEqual j (by omega)]
      exact failed j earlier
    · rw [blockEqual n le_rfl]
      exact hit

end ComplexityOfGenerators
