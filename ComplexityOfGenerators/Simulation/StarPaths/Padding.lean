import ComplexityOfGenerators.Simulation.StarPaths.Selection

namespace ComplexityOfGenerators.Simulation.StarPaths
set_option backward.isDefEq.respectTransparency true

private theorem cutWalk_append (count : ℕ) (bits extra : List Bool) (current : ℕ) (prior : Parts)
    (enough : count ≤ bits.length) :
    cutWalk count (bits++extra) current prior = cutWalk count bits current prior := by
  induction count generalizing bits current prior with
  | zero => rfl
  | succ count ih =>
      cases bits with
      | nil => simp at enough
      | cons bit rest =>
          cases bit <;> simp only [List.cons_append,cutWalk,List.getElem?_cons_zero,Option.getD_some,
            Bool.false_eq_true,ite_false,ite_true,List.tail_cons] <;>
            exact ih rest _ _ (by simpa using enough)

theorem proposal_append (n : ℕ) (bits extra : List Bool) (enough : n-1 ≤ bits.length) :
    proposal n (bits++extra) = proposal n bits := by
  unfold proposal
  split_ifs
  · rfl
  · exact cutWalk_append _ bits extra 1 [] enough

theorem selected_append (flags : List Bool) (n : ℕ) (bits extra : List Bool) (enough : n-1 ≤ bits.length) :
    selected flags n (bits++extra) = selected flags n bits := by
  simp only [selected,proposal_append n bits extra enough]

/-- Full support persists when the caller collects a larger fixed coin block. -/
theorem selected_full_support_padded (flags : List Bool) (n block : ℕ) (parts : Parts)
    (enough : n-1 ≤ block) (valid : Valid flags n parts) :
    ∃ bits : List Bool, bits.length = block ∧ selected flags n bits = some parts := by
  obtain ⟨bits,length,result⟩ := selected_full_support flags n parts valid
  refine ⟨bits++List.replicate (block-(n-1)) false,?_,?_⟩
  · simp only [List.length_append,List.length_replicate,length]
    omega
  · rw [selected_append flags n bits _ (by omega)]
    exact result

end ComplexityOfGenerators.Simulation.StarPaths
