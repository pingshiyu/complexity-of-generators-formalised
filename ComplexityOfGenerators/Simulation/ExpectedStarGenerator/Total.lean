import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Execution
import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.PathTotal

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

def GeneratedResult (n : ℕ) : Result (Cell M P) α 80 → Prop
  | .exhausted => True
  | .done after => ∃ parts : List ℕ, ∃ factors : List (List α), parts.sum = n ∧
      (∀ j ∈ parts, 0 < j) ∧ List.Forall₂ (fun j word => word ∈ P.layer j) parts factors ∧ after.output = factors.flatten

/-- Every finite random tape finishes, including when no productive
composition is certified or a later factor exhausts its available bits. -/
theorem command_runs_total (n random : ℕ) (bits : BitString) :
    ∃ ticks result, (command M p P).Runs n bits (initialMemory M P random) ticks result ∧ GeneratedResult M P n result := by
  unfold command
  obtain ⟨first, _, firstRun⟩ := boot_runs M P n random bits
  have readySize : StoreBound (readyMemory M P n random).store (CertifiedStarPhase.cap p n) :=
    (ready_bound M P n random).mono (by have := outer_indexBudget p n; omega)
  obtain ⟨second, result, secondRun, pathPost⟩ := pathRetry_runs_total M p P n bits (readyMemory M P n random) rfl rfl
    (ready_owned M P n random) readySize
  cases result with
  | exhausted =>
      exact ⟨first+1+second, .exhausted, Command.Runs.seq _ _ _ _ _ _ _ firstRun
        (Command.Runs.seq_absent _ _ _ _ secondRun), trivial⟩
  | done after =>
      obtain ⟨origin, empty, _, _, parts, total, positive, path⟩ := pathPost
      obtain ⟨last, result, lastRun, words⟩ := ExpectedStarCalls.generating_runs_total P (CertifiedStarPhase.encodePath M)
        (CertifiedStarPhase.projectPath M) (CertifiedStarPhase.project_encode M) n parts bits after origin empty path
        (fun j member => (part_le_sum parts j member).trans_eq total)
      refine ⟨first+1+(second+1+last), result, Command.Runs.seq _ _ _ _ _ _ _ firstRun
        (Command.Runs.seq _ _ _ _ _ _ _ secondRun lastRun), ?_⟩
      cases result with
      | exhausted => trivial
      | done next =>
          obtain ⟨factors, language, output⟩ := words
          exact ⟨parts, factors, total, positive, language, output⟩

/-- The actual finite-tape machine halts on every finite seed. Its accepted
outputs are precisely the word concatenations supplied by native source calls. -/
theorem machine_execution (n : ℕ) (bits : BitString) :
    ∃ ticks result, (machine M p P).run (generatorData n) bits ticks = .halted result.outcome ∧
      GeneratedResult M P n result := by
  obtain ⟨stackTicks, result, run, generated⟩ := command_runs_total M p P n 0 bits
  obtain ⟨ticks, _, native⟩ := compile_run M p P (run.executes 0)
  exact ⟨ticks, result, native, generated⟩

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
