import ComplexityOfGenerators.Examples.SATSelfReduction
import ComplexityOfGenerators.Proofs.SelfReduction

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

theorem nil_not_mem : ([] : List Symbol) ∉ language := by
  rw [word_mem_iff_certificates]
  simp

theorem word_reduce_member_length {word label : List Symbol}
    (member : wordReduce word label ∈ language) :
    (wordReduce word label).length = word.length := by
  cases decoded : decode word with
  | none => simp [wordReduce, decoded, nil_not_mem] at member
  | some result =>
    rcases result with ⟨M, d, f⟩
    obtain ⟨bound, valid, equal⟩ := decode_sound word M d f decoded
    cases d with
    | zero =>
      by_cases empty : label = []
      · simp [wordReduce, decoded, empty]
      · simp [wordReduce, decoded, empty, nil_not_mem] at member
    | succ d =>
      cases bit : labelValue label with
      | none => simp [wordReduce, decoded, bit, nil_not_mem] at member
      | some b =>
        have length := f.substitute_encoding_length bound b valid
        simp only [wordReduce, decoded, Nat.add_one_ne_zero, ite_false, bit,
          Nat.add_sub_cancel]
        exact length.trans (congrArg List.length equal)

theorem path_member_length {x y : List Symbol} (path : selfReduction.Path x y)
    (member : y ∈ language) : y.length = x.length := by
  induction path with
  | refl => rfl
  | @tail y z path step ih =>
    have intermediate := selfReduction.step_mem step member
    obtain ⟨label, _, _, reduction⟩ := step
    change wordReduce y label = z at reduction
    have same := word_reduce_member_length (by simpa only [← reduction] using member)
    have last : z.length = y.length := by simpa only [reduction] using same
    exact last.trans (ih intermediate)

/-- Every successful SAT reduction retains the full padded word length, so
the ancestor set is exactly the requested language slice. -/
theorem ancestors_eq_slice (n : ℕ) : selfReduction.ancestors n = lengthSlice language n := by
  apply Set.Subset.antisymm
  · intro word ancestor
    obtain ⟨member, source, sourceMember, path⟩ := selfReduction.mem_ancestors_iff.mp ancestor
    exact ⟨member, (path_member_length path member).trans sourceMember.2⟩
  · exact selfReduction.slice_subset_ancestors n

/-- Rank-zero initial outputs are precisely satisfiable constant formulas
whose padded encoding has the requested length. -/
theorem bases_eq (n : ℕ) :
    selfReduction.bases n = {word | ∃ M f, f.valid 0 ∧ Satisfiable 0 f ∧
      (f.encode M 0).length = n ∧ f.encode M 0 = word} := by
  ext word
  change (word ∈ selfReduction.ancestors n ∧ wordRank word = 0) ↔ _
  rw [ancestors_eq_slice]
  constructor
  · rintro ⟨⟨⟨M, d, f, bound, valid, sat, equal⟩, length⟩, rank⟩
    have zero : d = 0 := by
      rw [← equal, wordRank_encode bound f valid] at rank
      exact rank
    subst d
    exact ⟨M, f, valid, sat, by simpa [equal] using length, equal⟩
  · rintro ⟨M, f, valid, sat, length, rfl⟩
    exact ⟨⟨⟨M, 0, f, Nat.zero_le _, valid, sat, rfl⟩, length⟩,
      wordRank_encode (Nat.zero_le _) f valid⟩

end ComplexityOfGenerators.Examples.PaddedCNF
