import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
import ComplexityOfGenerators.Simulation.WordStack.Blocks
import ComplexityOfGenerators.Simulation.WordStack.LengthTest

namespace ComplexityOfGenerators.Simulation.WordStack

variable {S O : Type} {k : ℕ}

def StoreBound (s : Local.Store S k) (budget : ℕ) : Prop := ∀ j, (s j).length ≤ budget

namespace StoreBound

variable {s : Local.Store S k} {budget : ℕ}

theorem mono (h : StoreBound s budget) {larger : ℕ} (le : budget ≤ larger) : StoreBound s larger :=
  fun j => (h j).trans le

theorem update (h : StoreBound s budget) (j : Fin k) (word : List S) (size : word.length ≤ budget) :
    StoreBound (Function.update s j word) budget := by
  intro i
  by_cases equal : i = j
  · simpa [equal] using size
  · simpa [equal] using h i

theorem clear (h : StoreBound s budget) (j : Fin k) : StoreBound (Function.update s j []) budget :=
  h.update j [] (by simp)

theorem assign (h : StoreBound s budget) (src dst scratch : Fin k)
    (sd : src ≠ dst) (st : src ≠ scratch) (dt : dst ≠ scratch) (f : S → S) :
    StoreBound ((Routine.assign (O := O) src dst scratch sd st dt f).eval s) budget := by
  rw [Routine.assign_eval]
  exact (h.clear scratch).update dst _ (by simpa using h src)

theorem counter (h : StoreBound s budget) (slots : CounterRoutine.Layout k) (p : PolynomialBound) (unit : S)
    (base : (s (slots 0)).length + 1 ≤ budget) (value : p (s (slots 0)).length ≤ budget) :
    StoreBound ((CounterRoutine.routine (O := O) slots p unit).eval s) budget := by
  rw [CounterRoutine.routine_eval]
  exact (((h.clear (slots 4)).update (slots 2) _ (by simpa using base)).clear (slots 3)).update
    (slots 1) _ (by simpa using value)

theorem block (h : StoreBound s budget) (counter src dst : Fin k) (cs : counter ≠ src) (cd : counter ≠ dst)
    (sd : src ≠ dst) (empty : s dst = []) :
    StoreBound ((Blocks.routine (O := O) counter src dst cs cd).eval s) budget := by
  rw [Blocks.routine_eval counter src dst cs cd sd]
  apply ((h.clear counter).update src _ ?_).update dst _ ?_
  · simp only [List.length_drop]
    exact (Nat.sub_le _ _).trans (h src)
  · simp only [empty, List.append_nil, List.length_reverse, List.length_take]
    exact (Nat.min_le_right _ _).trans (h src)

theorem lengthTest (h : StoreBound s budget) (slots : LengthTest.Layout k) (unit : S) (positive : 1 ≤ budget) :
    StoreBound ((LengthTest.routine (O := O) slots unit).eval s) budget := by
  rw [LengthTest.routine_eval]
  apply (((h.clear (slots 5)).clear (slots 4)).clear (slots 3)).update
  split <;> simp_all

end StoreBound
end ComplexityOfGenerators.Simulation.WordStack
