import ComplexityOfGenerators.Simulation.WordStack.RandomFree
import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine

namespace ComplexityOfGenerators.Simulation.WordStack.Command
variable {S O : Type} {k : ℕ}

@[simp] theorem randomFree_prepend (dst : Fin k) (word : List S) : RandomFree (prepend (O := O) dst word) := by
  induction word with
  | nil => exact .skip
  | cons symbol rest ih => exact .seq ih (randomFree_push dst symbol)

@[simp] theorem randomFree_scale (value base temp scratch : Fin k) :
    RandomFree (scale (S := S) (O := O) value base temp scratch) := by
  simp [scale, multiply]

@[simp] theorem randomFree_power (value base temp scratch : Fin k) (degree : ℕ) :
    RandomFree (power (S := S) (O := O) value base temp scratch degree) := by
  induction degree with
  | zero => exact .skip
  | succ degree ih => exact .seq ih (randomFree_scale _ _ _ _)

@[simp] theorem randomFree_polynomialCounter (p : PolynomialBound) (value base temp scratch : Fin k) (unit : S) :
    RandomFree (polynomialCounter (O := O) p value base temp scratch unit) := by
  simp [polynomialCounter]

end ComplexityOfGenerators.Simulation.WordStack.Command
