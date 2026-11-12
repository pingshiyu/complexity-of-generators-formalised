import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Bounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Correctness
import ComplexityOfGenerators.Simulation.WordStack.RoutineWordFunction

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def time : PolynomialBound := PolynomialBound.ofPolynomial (50000000 * (Polynomial.X + 4)^2)

theorem loaded_bound (word label : List Symbol) : StoreBound (loadedStore word label) (word.length + label.length) := by
  intro j
  by_cases first : j = 0 <;> by_cases second : j = 1 <;> simp [loadedStore, first, second] <;> omega

theorem routine_time (word label : List Symbol) :
    (routine (O := Symbol)).cost (loadedStore word label) + 1 +
      4 * ((routine (O := Symbol)).eval (loadedStore word label) 31).length ≤
      time (word.length + label.length) := by
  obtain ⟨stored, cost⟩ := routine_bound (O := Symbol) (loadedStore word label) (word.length + label.length) (loaded_bound word label)
  have output := stored 31
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ (word.length + label.length))
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_pow]
  nlinarith only [cost, output]

/-- An actual deterministic polynomial word machine for the complete
HAMPATH forward reduction, including syntax, labels, edge tests and deletion. -/
noncomputable def computable : PolynomialWordFunction wordReduce := by
  apply Routine.polynomialWordFunction (routine (O := Symbol)) 0 1 0 31 (by decide) id id (fun symbol => some symbol)
    wordReduce time routine_randomFree
  · intro word label
    have loadedEq : (InputBank.loadedMemory (O := Symbol) (0 : Fin 32) 1 (id : Symbol → Symbol) id
        ({input := word, auxiliary := label} : InputData Symbol Symbol)).store = loadedStore word label := by
      simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loadedStore]
    rw [loadedEq, routine_value]
    simp
  · intro word label
    have loadedEq : (InputBank.loadedMemory (O := Symbol) (0 : Fin 32) 1 (id : Symbol → Symbol) id
        ({input := word, auxiliary := label} : InputData Symbol Symbol)).store = loadedStore word label := by
      simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loadedStore]
    simpa only [loadedEq] using routine_time word label

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
