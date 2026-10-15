import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Tape representation of Mathlib stacks

A stack occupies cells `0, …, length-1`, with its top at the right. The head
rests on the first blank cell. Popping erases the old top, so repeated stack
operations reuse the same region rather than accumulating a history.
-/

namespace ComplexityOfGenerators.Simulation.StackSpace

variable {S : Type}

/-- Bottom-to-top storage, with explicit blanks outside the stack. -/
def stackTape (xs : List S) (i : ℤ) : Option S :=
  if 0 ≤ i then xs.reverse[i.toNat]? else none

@[simp] theorem stackTape_nil (i : ℤ) : stackTape ([] : List S) i = none := by
  simp [stackTape]

@[simp] theorem stackTape_end (xs : List S) : stackTape xs xs.length = none := by
  simp [stackTape]

theorem stackTape_cons (a : S) (xs : List S) :
    stackTape (a :: xs) = Function.update (stackTape xs) (xs.length : ℤ) (some a) := by
  funext i
  by_cases h : i = (xs.length : ℤ)
  · subst i
    simp [stackTape, List.reverse_cons]
  · rw [Function.update_of_ne h]
    by_cases hi : 0 ≤ i
    · have hn : i.toNat ≠ xs.length := by omega
      simp only [stackTape, hi, ↓reduceIte, List.reverse_cons]
      by_cases hlt : i.toNat < xs.length
      · simp [List.getElem?_append, hlt]
      · have hgt : xs.length < i.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    · simp [stackTape, hi]

@[simp] theorem stackTape_top (a : S) (xs : List S) :
    stackTape (a :: xs) xs.length = some a := by
  rw [stackTape_cons, Function.update_self]

theorem stackTape_pop (a : S) (xs : List S) :
    Function.update (stackTape (a :: xs)) (xs.length : ℤ) none = stackTape xs := by
  rw [stackTape_cons, Function.update_idem, ← stackTape_end xs, Function.update_eq_self]

end ComplexityOfGenerators.Simulation.StackSpace
