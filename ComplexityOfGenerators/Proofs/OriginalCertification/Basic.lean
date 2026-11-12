import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler
import ComplexityOfGenerators.Foundations.ExpectedClosureBounds
import ComplexityOfGenerators.Foundations.FiniteBlockPhaseLists
import ComplexityOfGenerators.Simulation.UnionGenerator.Views

/-! Bounded certificates test productivity and discard their outputs before
the fresh original generation calls. A fourfold random budget is an exact
monomial and contains the entire doubled-time native test. -/
namespace ComplexityOfGenerators.OriginalCertification
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

def clock (p : PolynomialBound) : PolynomialBound :=
  ⟨2*p.coefficient,p.degree,Nat.mul_pos (by decide) p.coefficient_pos⟩
def seed (p : PolynomialBound) : PolynomialBound :=
  ⟨4*p.coefficient,p.degree,Nat.mul_pos (by decide) p.coefficient_pos⟩

@[simp] theorem clock_eval (p : PolynomialBound) (n : ℕ) : clock p n=2*p n := by
  simp [clock,PolynomialBound.eval,Nat.mul_assoc]
@[simp] theorem seed_eval (p : PolynomialBound) (n : ℕ) : seed p n=4*p n := by
  simp [seed,PolynomialBound.eval,Nat.mul_assoc]
theorem seed_fits (p : PolynomialBound) (n : ℕ) : clock p n+1≤seed p n := by
  have positive := p.positive n
  rw [clock_eval,seed_eval]
  omega

variable {α : Type}
def source (M : Machine Unit Bool α) (p : PolynomialBound) (j : ℕ) : FiniteBlockPhase α :=
  FiniteBlockPhase.fromList (seed p j) (UnionGenerator.sourceValue M (clock p) j)

abbrev marker {β : Type} (phase : FiniteBlockPhase α) (payload : List β) : FiniteBlockPhase β :=
  ⟨phase.width,fun bits => (phase.value bits).map (fun _ => payload)⟩

theorem marker_success {β : Type} (phase : FiniteBlockPhase α) (payload : List β) :
    (marker phase payload).successMass=phase.successMass := by
  unfold FiniteBlockPhase.successMass
  congr 1
  ext bits
  change ((phase.value bits).map (fun _ => payload)).isSome=true ↔ (phase.value bits).isSome=true
  cases phase.value bits <;> rfl

theorem marker_language {β : Type} (phase : FiniteBlockPhase α) (payload word : List β) :
    word∈(marker phase payload).language ↔ word=payload ∧ 0<phase.successMass := by
  classical
  by_cases equal : word=payload
  · subst word
    have events : {bits | (marker phase payload).value bits=some payload}=
        OptionPhase.success phase.value := by
      ext bits
      change ((phase.value bits).map (fun _ => payload))=some payload ↔ (phase.value bits).isSome=true
      cases phase.value bits <;> simp
    change 0<fairBlockMeasure phase.width {bits | (marker phase payload).value bits=some payload} ↔
      payload=payload ∧ 0<phase.successMass
    rw [events]
    simp only [FiniteBlockPhase.successMass,true_and]
  · have events : {bits | (marker phase payload).value bits=some word}=∅ := by
      ext bits
      change ((phase.value bits).map (fun _ => payload))=some word ↔ False
      cases phase.value bits <;> simp [Ne.symm equal]
    change 0<fairBlockMeasure phase.width {bits | (marker phase payload).value bits=some word} ↔
      word=payload ∧ 0<phase.successMass
    rw [events]
    simp [equal]

theorem source_sound (G : UniformGenerators α) (p : PolynomialBound) (j : ℕ)
    (bits : Fin (source G.machine p j).width → Bool) {word : List α}
    (produced : (source G.machine p j).value bits=some word) : word∈G.layer j := by
  have run : G.machine.run (generatorData j) (List.ofFn bits) (clock p j)=.halted (.accepted word) := by
    change (G.machine.run (generatorData j) (List.ofFn bits) (clock p j)).acceptedWord=some word at produced
    cases execution : G.machine.run (generatorData j) (List.ofFn bits) (clock p j) with
    | running current => simp only [execution,RunState.acceptedWord,reduceCtorEq] at produced
    | halted outcome =>
      cases outcome with
      | accepted output =>
        simp only [execution,RunState.acceptedWord,Outcome.acceptedWord,Option.some.injEq] at produced
        cases produced
        rfl
      | rejected => simp only [execution,RunState.acceptedWord,Outcome.acceptedWord,reduceCtorEq] at produced
      | exhausted => simp only [execution,RunState.acceptedWord,Outcome.acceptedWord,reduceCtorEq] at produced
  exact (G.machine.mem_generatedLanguage_iff_produces (generatorData j) word).mpr
    ⟨List.ofFn bits,clock p j,run⟩

theorem source_mass (M : Machine Unit Bool α) (p : PolynomialBound) (j : ℕ)
    (expected : M.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞)) :
    (1 : ℝ≥0∞)/2≤(source M p j).successMass := by
  have lower := M.bounded_prefix_acceptance_ge_half (generatorData j) (p j) (p.positive j) expected
  have enlarge : {stream | ∃ word,M.run (generatorData j) (streamPrefix stream (2*p j+1)) (2*p j)=
      .halted (.accepted word)} ⊆
      {stream | ∃ word,M.run (generatorData j) (streamPrefix stream (seed p j)) (clock p j)=
        .halted (.accepted word)} := by
    rintro stream ⟨word,run⟩
    refine ⟨word,?_⟩
    rw [clock_eval,M.run_streamPrefix_eq_of_not_exhausted (generatorData j)
      (stream_mem_prefix_cylinder stream (2*p j+1)) (by have := seed_fits p j; simp only [clock_eval] at this; omega)
      (by simp [run]),run]
  have events : {stream | ∃ word,M.run (generatorData j) (streamPrefix stream (seed p j)) (clock p j)=
        .halted (.accepted word)}=
      {stream | (splitStream (seed p j) stream).1∈OptionPhase.success (source M p j).value} := by
    ext stream
    change (∃ word,M.run (generatorData j) (streamPrefix stream (seed p j)) (clock p j)=.halted (.accepted word)) ↔
      (M.run (generatorData j) (streamPrefix stream (seed p j)) (clock p j)).acceptedWord.isSome=true
    cases execution : M.run (generatorData j) (streamPrefix stream (seed p j)) (clock p j) with
    | running current => simp only [RunState.acceptedWord,Option.isSome_none,Bool.false_eq_true,reduceCtorEq,exists_false]
    | halted outcome => cases outcome <;> simp [RunState.acceptedWord,Outcome.acceptedWord]
  have law := fairCoinMeasure_prefix_tail (seed p j) (OptionPhase.success (source M p j).value)
    Set.univ (Set.to_countable _ |>.measurableSet) MeasurableSet.univ
  simp only [Set.mem_univ,and_true,measure_univ,mul_one] at law
  apply (lower.trans (measure_mono enlarge)).trans_eq
  rw [events]
  exact law

theorem source_positive_iff (G : UniformGenerators α) (p : PolynomialBound) (j : ℕ)
    (expected : (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞)) :
    0<(source G.machine p j).successMass ↔ (G.layer j).Nonempty := by
  constructor
  · intro positive
    obtain ⟨bits,produced⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
    obtain ⟨word,equal⟩ := Option.isSome_iff_exists.mp produced
    exact ⟨word,source_sound G p j bits equal⟩
  · intro active
    exact (by norm_num : (0 : ℝ≥0∞)<1/2).trans_le (source_mass G.machine p j (expected active))

end
end ComplexityOfGenerators.OriginalCertification
