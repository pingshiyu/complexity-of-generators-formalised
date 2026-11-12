import ComplexityOfGenerators.Simulation.ExactRecursive.Program
import ComplexityOfGenerators.Simulation.ExactRecursive.TrialBounds
import ComplexityOfGenerators.Proofs.CommandGenerators
import ComplexityOfGenerators.Simulation.WordStack.BoundedInput

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def preparedMemory (n read : ℕ) (bits : BitString) : Memory (Cell B V) α 35 :=
  ⟨(), n, read, [], Function.update
    (Function.update (Function.update (fun _ => []) 13 (List.replicate n Symbol.unit))
      19 (List.replicate (n + 1) Symbol.unit)) 17 (bits.map Symbol.bit)⟩

noncomputable def prepareBudget (seed : PolynomialBound) (n : ℕ) : ℕ :=
  29 * n + 12 * seed n + Command.counterBudget seed n + 12

theorem prepare_runs (seed : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∃ t ≤ prepareBudget seed n,
      (prepareCommand B V seed).Runs n bits Command.emptyMemory t
        (if seed n ≤ bits.length then .done (preparedMemory B V n (seed n) (bits.take (seed n))) else .exhausted) := by
  exact BoundedSource.prepare_runs (O := α) (Symbol.unit : Cell B V) Symbol.bit seed n bits

end ComplexityOfGenerators.Simulation.ExactRecursive
