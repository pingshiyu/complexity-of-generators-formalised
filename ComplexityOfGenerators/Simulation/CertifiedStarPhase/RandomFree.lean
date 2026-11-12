import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Phase

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true

/-- The alphabet-preparation prefix and mapped DP only inspect the already
collected coin word; they request no additional random bits. -/
theorem canonicalPrepare_randomFree : (canonicalPrepare M).command.RandomFree := by
  simp [canonicalPrepare,normalize]

theorem pathStage_randomFree : (pathStage M).command.RandomFree := by
  change ((canonicalPrepare M).command.seq (mappedCommand M)).RandomFree
  apply Command.RandomFree.seq (canonicalPrepare_randomFree M)
  unfold mappedCommand
  exact (StarPaths.pathRoutine_randomFree (O := α)).mapSymbols (encodePath M) (projectPath M)

theorem routine_randomFree (p : PolynomialBound) : (routine M p).command.RandomFree := by
  exact (WordStack.Routine.randomFree_seq _ _).mpr
    ⟨StarCertification.routine_randomFree M p,pathStage_randomFree M⟩

end ComplexityOfGenerators.Simulation.CertifiedStarPhase
