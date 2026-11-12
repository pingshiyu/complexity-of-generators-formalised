import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare

namespace ComplexityOfGenerators.Simulation.WordStack.StoreBound

variable {S O : Type} {k : ℕ} {s : Local.Store S k} {budget : ℕ}

theorem strictCompare (sizes : StoreBound s budget) (slots : RationalSelection.Compare.Layout k)
    (unit : S) (positive : 1 ≤ budget) :
    StoreBound ((RationalSelection.Compare.routine (O := O) slots unit).eval s) budget := by
  rw [RationalSelection.Compare.routine_eval]
  apply (((sizes.clear (slots 5)).clear (slots 4)).clear (slots 3)).update (slots 2)
  split
  · simpa using positive
  · simp

end ComplexityOfGenerators.Simulation.WordStack.StoreBound
