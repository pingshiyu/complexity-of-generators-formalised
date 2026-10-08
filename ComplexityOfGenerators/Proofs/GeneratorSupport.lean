import ComplexityOfGenerators.Foundations.RandomTape
import ComplexityOfGenerators.Foundations.Probability

/-!
# Generator support and productivity

An output in the generated language has positive probability: its accepting
seed contributes a positive-measure cylinder. Consequently, the paper's
zero-or-one productivity condition is one precisely for nonempty languages.
The empty seed causes no boundary exception, because accepting it implies
acceptance on every nonempty extension.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

theorem cylinder_mono_prefix {short long : BitString} (hprefix : short <+: long) :
    cylinder long ⊆ cylinder short := by
  obtain ⟨tail, rfl⟩ := hprefix
  intro stream member i
  have bound : i.val < (short ++ tail).length := by simp; omega
  have equal := member ⟨i.val, bound⟩
  change stream i.val = short[i.val]
  simpa using equal

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

theorem generatedLanguage_nonempty_iff_accepts :
    (M.generatedLanguage data).Nonempty ↔ ∃ bits, M.Accepts data bits := by
  constructor
  · rintro ⟨word, bits, nonempty, produces⟩
    exact ⟨bits, word, produces⟩
  · rintro ⟨bits, word, produces⟩
    refine ⟨word, bits ++ [false], ?_, M.produces_append data bits [false] word produces⟩
    simp

theorem cylinder_subset_acceptedStreams (bits : BitString) (accepted : M.Accepts data bits) :
    cylinder bits ⊆ M.acceptedStreams data := fun _stream member => ⟨bits, member, accepted⟩

theorem positive_acceptance_of_nonempty (nonempty : (M.generatedLanguage data).Nonempty) :
    0 < fairCoinMeasure (M.acceptedStreams data) := by
  obtain ⟨bits, accepted⟩ := (M.generatedLanguage_nonempty_iff_accepts data).mp nonempty
  have lower : fairCoinMeasure (cylinder bits) ≤ fairCoinMeasure (M.acceptedStreams data) :=
    measure_mono (M.cylinder_subset_acceptedStreams data bits accepted)
  rw [fairCoinMeasure_cylinder] at lower
  have base : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by norm_num
  have positive : 0 < (2 : ℝ≥0∞)⁻¹ ^ bits.length :=
    bot_lt_iff_ne_bot.mpr (pow_ne_zero _ base)
  exact positive.trans_le lower

theorem acceptedStreams_eq_empty_iff :
    M.acceptedStreams data = ∅ ↔ M.generatedLanguage data = ∅ := by
  constructor
  · intro empty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro word member
    have positive := M.positive_acceptance_of_nonempty data ⟨word, member⟩
    simp [empty] at positive
  · intro empty
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro stream ⟨bits, cylinderMember, accepted⟩
    have nonempty := (M.generatedLanguage_nonempty_iff_accepts data).mpr ⟨bits, accepted⟩
    simp [empty] at nonempty

theorem generator_probability_one_iff_nonempty (generator : M.IsGenerator data) :
    fairCoinMeasure (M.acceptedStreams data) = 1 ↔ (M.generatedLanguage data).Nonempty := by
  constructor
  · intro productive
    by_contra empty
    have languageEmpty := Set.not_nonempty_iff_eq_empty.mp empty
    have eventEmpty := (M.acceptedStreams_eq_empty_iff data).mpr languageEmpty
    simp [eventEmpty] at productive
  · intro nonempty
    rcases generator.2 with productive | unproductive
    · exact productive
    · have positive := M.positive_acceptance_of_nonempty data nonempty
      rw [unproductive] at positive
      exact False.elim (lt_irrefl _ positive)

/-- The minimal-prefix condition used in the paper's acceptance event. The
empty prefix is permitted when the machine accepts without reading randomness. -/
def MinimalAcceptedSeed (bits : BitString) : Prop :=
  M.Accepts data bits ∧ ∀ k < bits.length, ¬ M.Accepts data (bits.take k)

theorem exists_minimal_accepted_prefix (bits : BitString) (accepted : M.Accepts data bits) :
    ∃ short, short <+: bits ∧ M.MinimalAcceptedSeed data short := by
  classical
  have existsLength : ∃ k : ℕ, k ≤ bits.length ∧ M.Accepts data (bits.take k) :=
    ⟨bits.length, le_rfl, by simpa using accepted⟩
  let k := Nat.find existsLength
  obtain ⟨bound, accepts⟩ := Nat.find_spec existsLength
  have kBound : k ≤ bits.length := bound
  have length : (bits.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left kBound]
  refine ⟨bits.take k, List.take_prefix k bits, accepts, ?_⟩
  intro j less smaller
  rw [length] at less
  apply Nat.find_min existsLength less
  refine ⟨by omega, ?_⟩
  simpa [List.take_take, Nat.min_eq_left less.le] using smaller

/-- Our accepted-prefix event is exactly the paper's union over minimal
accepted prefixes. This includes machines accepting on the empty prefix. -/
theorem acceptedStreams_eq_minimal_prefixes :
    M.acceptedStreams data =
      {stream | ∃ bits, stream ∈ cylinder bits ∧ M.MinimalAcceptedSeed data bits} := by
  ext stream
  constructor
  · rintro ⟨bits, member, accepted⟩
    obtain ⟨short, hprefix, minimal⟩ := M.exists_minimal_accepted_prefix data bits accepted
    exact ⟨short, cylinder_mono_prefix hprefix member, minimal⟩
  · rintro ⟨bits, member, accepted, minimal⟩
    exact ⟨bits, member, accepted⟩

end Machine

end ComplexityOfGenerators
