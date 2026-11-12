import ComplexityOfGenerators.Examples.SATInverseWords
import ComplexityOfGenerators.Examples.HAMPATHInverseWords

namespace ComplexityOfGenerators

theorem SelfReduction.width_le_rank_on_member {α : Type} {L : Language α} (R : SelfReduction L)
    {word : Word α} (member : word ∈ L) : R.width word ≤ R.rank word := by
  obtain ⟨certificate, good⟩ := (R.certifies word).mp member
  obtain ⟨label, tail, width, _, equal⟩ := (R.split word certificate).mp good
  have length := R.certificate_length word certificate good
  rw [equal, List.length_append, width] at length
  omega

theorem SelfReduction.inverse_input_bounds {α : Type} {L : Language α} (R : SelfReduction L)
    (rankBound : ∀ word, R.rank word ≤ word.length) {n : ℕ} {target label source : Word α}
    (member : source ∈ R.inverseFibre n target label) : target.length ≤ n ∧ label.length ≤ n := by
  obtain ⟨ancestor, reduction, width⟩ := member
  have sourceSize := R.ancestor_length_le ancestor
  have targetSize := R.length_reduce source label
  rw [reduction] at targetSize
  have widthRank := R.width_le_rank_on_member ancestor.1
  rw [← width] at widthRank
  have rankSize := rankBound source
  omega

theorem SelfReduction.inverse_empty_of_oversized_input {α : Type} {L : Language α} (R : SelfReduction L)
    (rankBound : ∀ word, R.rank word ≤ word.length) (n : ℕ) (target label : Word α)
    (oversized : n < target.length ∨ n < label.length) : R.inverseFibre n target label = ∅ := by
  ext source
  constructor
  · intro member
    have bounds := R.inverse_input_bounds rankBound member
    rcases oversized with oversized | oversized <;> omega
  · intro empty; exact False.elim empty

namespace Examples.PaddedCNF

theorem inverse_empty_of_oversized_input (n : ℕ) (target label : List Symbol)
    (oversized : n < target.length ∨ n < label.length) : selfReduction.inverseFibre n target label = ∅ :=
  selfReduction.inverse_empty_of_oversized_input word_rank_bound n target label oversized

end Examples.PaddedCNF

namespace Examples.HAMPATH

theorem inverse_empty_of_oversized_input (n : ℕ) (target label : List Symbol)
    (oversized : n < target.length ∨ n < label.length) : selfReduction.inverseFibre n target label = ∅ :=
  selfReduction.inverse_empty_of_oversized_input word_rank_bound n target label oversized

end Examples.HAMPATH
end ComplexityOfGenerators
