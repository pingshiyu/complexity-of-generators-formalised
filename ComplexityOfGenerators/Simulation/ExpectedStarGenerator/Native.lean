import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Total
import ComplexityOfGenerators.Proofs.FixedBlockRetryCriteria

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

theorem machine_runs_trace (n failures : ℕ) (parts : List ℕ) (records : List (ExpectedStarCalls.Record α))
    (bits : BitString) (total : parts.sum = n) (positive : ∀ j ∈ parts, 0 < j)
    (enough : (failures+1)*StarCertification.width p n ≤ bits.length)
    (failed : ∀ k < failures, CertifiedStarPhase.value M p n
      ((bits.drop (k*StarCertification.width p n)).take (StarCertification.width p n)) = none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (failures*StarCertification.width p n)).take (StarCertification.width p n)) = some (StarPaths.payload parts))
    (trace : ExpectedStarCalls.Trace P bits ((failures+1)*StarCertification.width p n) parts records) :
    ∃ ticks ≤ 25*(primitiveCoefficient M p P n)^2*(failures+1+ExpectedStarCalls.blocks records+1)^2,
      (machine M p P).run (generatorData n) bits ticks = .halted (.accepted (ExpectedStarCalls.words records)) := by
  obtain ⟨stackTicks, stackCost, next, run, output, _, _⟩ := command_runs_trace M p P n 0 failures parts records bits
    total positive (by simpa using enough) (by simpa using failed) (by simpa using success) (by simpa using trace)
  obtain ⟨ticks, compilerCost, native⟩ := compile_run M p P (run.executes 0)
  have deadline := Machine.retry_compiler_cost_le stackTicks (primitiveCoefficient M p P n)
    (failures+1+ExpectedStarCalls.blocks records) ((primitiveCoefficient M p P).positive n) stackCost
  refine ⟨ticks, compilerCost.trans deadline, ?_⟩
  simpa only [Result.outcome, output] using native

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
