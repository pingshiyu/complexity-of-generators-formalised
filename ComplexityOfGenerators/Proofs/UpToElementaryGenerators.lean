import ComplexityOfGenerators.Proofs.UpToGeneration
import ComplexityOfGenerators.Proofs.GeneratorCriteria
import ComplexityOfGenerators.Proofs.ElementaryGenerators

/-! Concrete cumulative families for the two boundary languages.  Their
finite-control machines are shared by the time and space results. -/

namespace ComplexityOfGenerators

noncomputable section
set_option backward.isDefEq.respectTransparency false

def emptyUpToFamily (α : Type) [Fintype α] : UpToGeneratorFamily α ∅ := by
  have language (n : ℕ) : (emptyGenerator α).generatedLanguage (generatorData n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro word ⟨bits, _, ticks, produced⟩
    rw [emptyGenerator_run] at produced
    split_ifs at produced <;> cases produced
  have generator (n : ℕ) : (emptyGenerator α).IsGenerator (generatorData n) := by
    apply Machine.isGenerator_of_full_trials _ _ 1
    · constructor
      · intro bits
        exact ⟨bits.length, .exhausted, by simp [emptyGenerator_run]⟩
      · intro bits ticks
        rw [emptyGenerator_run]
        split_ifs <;> simp
    · intro bits _
      rw [language]
      simp only [Set.not_nonempty_empty, iff_false]
      rintro ⟨word, ticks, accepted⟩
      rw [emptyGenerator_run] at accepted
      split_ifs at accepted <;> cases accepted
  refine { machine := emptyGenerator α, isGenerator := generator, layers := ?_ }
  intro n
  simpa [UniformGenerators.layer, upToSlice] using language n

def emptyWordUpToFamily (α : Type) [Fintype α] : UpToGeneratorFamily α {[]} := by
  let M := wordEmitter ([] : List α)
  have execution (n : ℕ) (bits : BitString) (ticks : ℕ) :
      M.run (generatorData n) bits ticks = .halted (.accepted []) := by
    have initial : M.run (generatorData n) bits 0 = .halted (.accepted []) := rfl
    simpa only [Nat.zero_add] using M.run_halted_add _ bits 0 _ initial ticks
  have language (n : ℕ) : M.generatedLanguage (generatorData n) = {[]} := by
    ext word
    constructor
    · rintro ⟨bits, _, ticks, accepted⟩
      rw [execution] at accepted
      simpa using accepted.symm
    · intro member
      have empty : word = [] := member
      subst word
      exact ⟨[false], by simp, 0, execution n [false] 0⟩
  have generator (n : ℕ) : M.IsGenerator (generatorData n) := by
    apply Machine.isGenerator_of_full_trials _ _ 1
    · constructor
      · intro bits
        exact ⟨0, .accepted [], execution n bits 0⟩
      · intro bits ticks
        rw [execution]
        simp
    · intro bits _
      rw [language]
      constructor
      · intro _
        exact ⟨[], rfl⟩
      · intro _
        exact ⟨[], 0, execution n bits 0⟩
  refine { machine := M, isGenerator := generator, layers := ?_ }
  intro n
  rw [show ({ machine := M, isGenerator := generator } : UniformGenerators α).layer n = {[]} from language n]
  ext word
  simp [upToSlice]
  rintro rfl
  simp

end
end ComplexityOfGenerators
