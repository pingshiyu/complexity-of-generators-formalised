import ComplexityOfGenerators.Proofs.GeneratorSupport
import ComplexityOfGenerators.Foundations.ExecutionBounds
import ComplexityOfGenerators.Foundations.BoundedGeneration
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Output length and runtime on the actual fair-coin stream

These quantities are derived from the native finite-control evaluator. A stream
has an output precisely when an accepting finite prefix exists. Runtime counts
primitive transitions, and is infinite when there is no accepting execution.
The output length is zero on divergence, as in the manuscript.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

def streamProduces (stream : BitStream) (word : List O) : Prop :=
  ∃ bits, stream ∈ cylinder bits ∧ M.Produces data bits word

def streamAcceptsBy (stream : BitStream) (time : ℕ) : Prop :=
  ∃ bits word, stream ∈ cylinder bits ∧
    M.run data bits time = .halted (.accepted word)

theorem cylinder_prefix_comparable {stream : BitStream} {a b : BitString}
    (ha : stream ∈ cylinder a) (hb : stream ∈ cylinder b) (length : a.length ≤ b.length) :
    a <+: b := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left length]
  · intro i hi hj
    have ib : i < b.length := lt_of_lt_of_le hi length
    have eqA := ha ⟨i, hi⟩
    have eqB := hb ⟨i, ib⟩
    change stream i = a[i] at eqA
    change stream i = b[i] at eqB
    simpa only [List.getElem_take] using eqA.symm.trans eqB

theorem streamProduces_unique {stream : BitStream} {a b : List O}
    (ha : M.streamProduces data stream a) (hb : M.streamProduces data stream b) : a = b := by
  obtain ⟨sa, ca, pa⟩ := ha
  obtain ⟨sb, cb, pb⟩ := hb
  rcases le_total sa.length sb.length with short | short
  · exact M.produces_unique data sb a b
      (M.produces_prefix (cylinder_prefix_comparable ca cb short) pa) pb
  · exact M.produces_unique data sa a b pa
      (M.produces_prefix (cylinder_prefix_comparable cb ca short) pb)

def streamLengthEvent (length : ℕ) : Set BitStream :=
  {stream | ∃ word, M.streamProduces data stream word ∧ word.length = length}

theorem measurableSet_streamLengthEvent (length : ℕ) :
    MeasurableSet (M.streamLengthEvent data length) := by
  classical
  have description : M.streamLengthEvent data length =
      ⋃ bits : BitString, ⋃ (_ : ∃ word, M.Produces data bits word ∧ word.length = length),
        cylinder bits := by
    ext stream
    simp only [streamLengthEvent, streamProduces, Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [description]
  exact MeasurableSet.iUnion fun bits => MeasurableSet.iUnion fun _ => measurableSet_cylinder bits

theorem streamLengthEvent_unique {stream : BitStream} {a b : ℕ}
    (ha : stream ∈ M.streamLengthEvent data a) (hb : stream ∈ M.streamLengthEvent data b) : a = b := by
  obtain ⟨wa, pa, la⟩ := ha
  obtain ⟨wb, pb, lb⟩ := hb
  have same := M.streamProduces_unique data pa pb
  rw [same] at la
  exact la.symm.trans lb

def streamLengthValue (stream : BitStream) (length : ℕ) : Prop :=
  stream ∈ M.streamLengthEvent data length ∨
    (length = 0 ∧ stream ∉ M.acceptedStreams data)

theorem streamLengthValue_exists (stream : BitStream) :
    ∃ length, M.streamLengthValue data stream length := by
  classical
  by_cases accepted : stream ∈ M.acceptedStreams data
  · obtain ⟨bits, member, word, produces⟩ := accepted
    exact ⟨word.length, Or.inl ⟨word, ⟨bits, member, produces⟩, rfl⟩⟩
  · exact ⟨0, Or.inr ⟨rfl, accepted⟩⟩

noncomputable def streamLength (stream : BitStream) : ℕ := by
  classical
  exact Nat.find (M.streamLengthValue_exists data stream)

theorem streamLength_spec (stream : BitStream) :
    M.streamLengthValue data stream (M.streamLength data stream) := by
  classical
  exact Nat.find_spec (M.streamLengthValue_exists data stream)

theorem streamLength_of_produces {stream : BitStream} {word : List O}
    (produces : M.streamProduces data stream word) : M.streamLength data stream = word.length := by
  rcases M.streamLength_spec data stream with length | ⟨zero, absent⟩
  · exact M.streamLengthEvent_unique data length ⟨word, produces, rfl⟩
  · obtain ⟨bits, member, produces⟩ := produces
    exact False.elim (absent ⟨bits, member, word, produces⟩)

theorem measurable_streamLength : Measurable (M.streamLength data) := by
  classical
  apply measurable_find (M.streamLengthValue_exists data)
  intro length
  by_cases h : length = 0
  · have description : {stream | M.streamLengthValue data stream length} =
        M.streamLengthEvent data 0 ∪ (M.acceptedStreams data)ᶜ := by
      ext stream
      simp only [streamLengthValue, h, true_and, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [description]
    exact (M.measurableSet_streamLengthEvent data 0).union
      (M.measurableSet_acceptedStreams data).compl
  · have description : {stream | M.streamLengthValue data stream length} =
        M.streamLengthEvent data length := by
      ext stream
      simp only [streamLengthValue, h, false_and, or_false, Set.mem_ofPred_eq]
    rw [description]
    exact M.measurableSet_streamLengthEvent data length

theorem streamAcceptsBy_mono {stream : BitStream} {a b : ℕ} (le : a ≤ b)
    (accepted : M.streamAcceptsBy data stream a) : M.streamAcceptsBy data stream b := by
  obtain ⟨bits, word, member, run⟩ := accepted
  refine ⟨bits, word, member, ?_⟩
  simpa [Nat.add_sub_of_le le] using M.run_halted_add data bits a (.accepted word) run (b-a)

theorem measurableSet_streamAcceptsBy (time : ℕ) :
    MeasurableSet {stream | M.streamAcceptsBy data stream time} := by
  classical
  have description : {stream | M.streamAcceptsBy data stream time} =
      ⋃ bits : BitString, ⋃ (_ : ∃ word,
        M.run data bits time = .halted (.accepted word)), cylinder bits := by
    ext stream
    simp only [streamAcceptsBy, Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [description]
  exact MeasurableSet.iUnion fun bits => MeasurableSet.iUnion fun _ => measurableSet_cylinder bits

noncomputable def streamRuntime (stream : BitStream) : ℝ≥0∞ := by
  classical
  exact ∑' time : ℕ, if M.streamAcceptsBy data stream time then 0 else 1

theorem measurable_streamRuntime : Measurable (M.streamRuntime data) := by
  classical
  apply Measurable.ennreal_tsum
  intro time
  exact measurable_const.piecewise (M.measurableSet_streamAcceptsBy data time) measurable_const

theorem streamRuntime_le_of_acceptsBy {stream : BitStream} {time : ℕ}
    (accepted : M.streamAcceptsBy data stream time) : M.streamRuntime data stream ≤ time := by
  classical
  unfold streamRuntime
  rw [tsum_eq_sum (s := Finset.range time)]
  · calc
      ∑ t ∈ Finset.range time, (if M.streamAcceptsBy data stream t then (0:ℝ≥0∞) else 1)
          ≤ ∑ _t ∈ Finset.range time, (1:ℝ≥0∞) := by
            apply Finset.sum_le_sum
            intro t ht
            split_ifs <;> simp
      _ = time := by simp
  · intro t ht
    have past : time ≤ t := by simpa only [Finset.mem_range, not_lt] using ht
    simp [M.streamAcceptsBy_mono data past accepted]

theorem acceptsBy_of_streamRuntime_le {stream : BitStream} {time : ℕ}
    (bound : M.streamRuntime data stream ≤ time) : M.streamAcceptsBy data stream time := by
  classical
  by_contra absent
  have lower : ((time + 1 : ℕ) : ℝ≥0∞) ≤ M.streamRuntime data stream := by
    have summands : ∀ t ∈ Finset.range (time+1),
        (if M.streamAcceptsBy data stream t then (0:ℝ≥0∞) else 1) = 1 := by
      intro t ht
      have le : t ≤ time := by simpa using (Finset.mem_range.mp ht)
      have no : ¬ M.streamAcceptsBy data stream t := fun yes => absent (M.streamAcceptsBy_mono data le yes)
      simp [no]
    have sumBound := ENNReal.sum_le_tsum (Finset.range (time+1))
      (f := fun t => if M.streamAcceptsBy data stream t then (0:ℝ≥0∞) else 1)
    simpa only [streamRuntime, Finset.sum_congr rfl summands, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] using sumBound
  have impossible := lower.trans bound
  exact (show ¬ ((time+1:ℕ):ℝ≥0∞) ≤ (time:ℝ≥0∞) by exact_mod_cast (Nat.not_succ_le_self time)) impossible

noncomputable def expectedLength : ℝ≥0∞ :=
  ∫⁻ stream, (M.streamLength data stream : ℝ≥0∞) ∂fairCoinMeasure

noncomputable def expectedRuntime : ℝ≥0∞ :=
  ∫⁻ stream, M.streamRuntime data stream ∂fairCoinMeasure

end Machine

end ComplexityOfGenerators
