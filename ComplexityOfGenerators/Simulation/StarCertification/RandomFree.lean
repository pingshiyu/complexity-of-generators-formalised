import ComplexityOfGenerators.Simulation.StarCertification.Basic
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

private theorem prepend_randomFree {S O : Type} {k : ℕ} (dst : Fin k) (word : List S) :
    (Command.prepend (O := O) dst word).RandomFree := by
  induction word with
  | nil => simp [Command.prepend]
  | cons symbol rest ih => simp [Command.prepend,ih]

private theorem power_randomFree {S O : Type} {k : ℕ} (value base temp scratch : Fin k) (degree : ℕ) :
    (Command.power (S := S) (O := O) value base temp scratch degree).RandomFree := by
  induction degree with
  | zero => simp [Command.power]
  | succ degree ih => simp [Command.power,Command.scale,Command.multiply,ih]

private theorem counter_randomFree {S O : Type} {k : ℕ} (slots : CounterRoutine.Layout k)
    (p : PolynomialBound) (unit : S) : (CounterRoutine.routine (O := O) slots p unit).command.RandomFree := by
  simp [CounterRoutine.routine,CounterRoutine.setup,Command.polynomialCounter,prepend_randomFree,power_randomFree]

/-- All source randomness is read from the previously collected block in
register17. The finite certification controller requests no further coins. -/
theorem routine_randomFree {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) :
    (routine M p).command.RandomFree := by
  simp [routine,prepare,scan,body,bodyPrefix,record,finish,trial,BoundedSource.sourceTrial,BoundedSource.counter,
    counter_randomFree,Blocks.routine,Blocks.body,Source.call,Source.prepare,apply_ite]

end ComplexityOfGenerators.Simulation.StarCertification
