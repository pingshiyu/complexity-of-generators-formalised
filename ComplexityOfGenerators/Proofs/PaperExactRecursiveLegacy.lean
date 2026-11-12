import ComplexityOfGenerators.Proofs.PaperExactRecursiveTrials

/-! Existing all-label, trial-budget constructions satisfy the current
paper's weaker bounded-label, accepting-time interface. -/
namespace ComplexityOfGenerators
noncomputable section

namespace ExactRecursiveGenerators
variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}

theorem nonempty_paper (G : ExactRecursiveGenerators R) :
    Nonempty (PaperExactRecursiveGenerators R) := by
  obtain ⟨baseSeed,baseTime,bounded⟩ := G.baseTime
  refine ⟨{
    labelBound := fun n=>R.logCoefficient*Nat.log 2 (n+1)+R.logConstant
    logCoefficient := R.logCoefficient
    logConstant := R.logConstant
    labelBound_log := fun _=>le_rfl
    width_le := ?_
    base := G.base
    baseTime := baseTime
    base_language := G.base_language
    base_time := ?_
    inverse := G.inverse
    inverseTime := G.inverseTime
    inverse_generator := fun n y w member _=>G.inverse_generator n y w member
    inverse_language := fun n y w member _=>G.inverse_language n y w member
    inverse_time := ?_ }⟩
  · intro n x size
    exact (R.width_le x).trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.log_mono_right (Nat.add_le_add_right size 1))) _)
  · intro n
    exact G.base.machine.generatorTimeBound_acceptingTimeBound _ _ _ (bounded n)
  · intro n y w member label
    exact G.inverse.generatorTimeBound_acceptingTimeBound _ _ _ (G.inverse_time n y w member)

end ExactRecursiveGenerators

theorem paperExactlyRecursivelyGenerable_of_legacy {α : Type} [Fintype α] {L : Language α}
    (generable : ExactlyRecursivelyGenerable L) : PaperExactlyRecursivelyGenerable L := by
  obtain ⟨R,polynomial,⟨G⟩⟩ := generable
  exact ⟨R,polynomial,G.nonempty_paper⟩

end
end ComplexityOfGenerators
