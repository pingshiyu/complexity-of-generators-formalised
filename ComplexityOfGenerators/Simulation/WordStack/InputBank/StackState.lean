import ComplexityOfGenerators.Simulation.WordStack.InputBank.Basic

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank

open TransducerBank

set_option backward.isDefEq.respectTransparency false

def stackState {Q S O : Type} {k : ℕ} (state : Q) (store : Fin k → List S)
    (inputHead auxiliaryHead : ℕ) : BankConfiguration O Q (Option S) k :=
  ⟨state, inputHead, auxiliaryHead, 0, 0, [], fun j => (store j).length, fun j => tape (store j)⟩

/-- Two bank instructions perform a genuine single-symbol stack push. The
first moves to the fresh cell and the second writes the letter there. -/
theorem push_stackState {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q (Option S) k)
    (data : InputData I A) (store : Fin k → List S) (j : Fin k)
    (current pending next : Q) (letter : S) (input auxiliary : Move) (inputHead auxiliaryHead : ℕ)
    (inputBound : inputHead ≤ data.input.length) (auxiliaryBound : auxiliaryHead ≤ data.auxiliary.length)
    (firstSelected : B.select current = j) (lastSelected : B.select pending = j) :
    B.advance data
      (B.advance data (stackState current store inputHead auxiliaryHead) pending
        (tape (store j) (store j).length) .right input auxiliary .stay none)
      next (some letter) .stay .stay .stay .stay none =
      stackState next (Function.update store j (letter :: store j))
        (input.onInput data.input.length inputHead) (auxiliary.onInput data.auxiliary.length auxiliaryHead) := by
  apply BankConfiguration.ext
  · rfl
  · change min (input.onInput data.input.length inputHead) data.input.length = _
    exact Nat.min_eq_left (input.onInput_le _ _ inputBound)
  · change min (auxiliary.onInput data.auxiliary.length auxiliaryHead) data.auxiliary.length = _
    exact Nat.min_eq_left (auxiliary.onInput_le _ _ auxiliaryBound)
  · simp [TapeBank.advance, stackState, Move.onInput]
  · rfl
  · rfl
  · funext a
    by_cases same : a = j
    · subst a
      simp [TapeBank.advance, stackState, firstSelected, lastSelected, Move.onInt]
    · simp [TapeBank.advance, stackState, firstSelected, lastSelected, same]
  · funext a
    by_cases same : a = j
    · subst a
      simp only [TapeBank.advance, stackState, firstSelected, lastSelected, Function.update_self,
        Move.onInt, Function.update_eq_self]
      exact (tape_push (store j) letter).symm
    · simp [TapeBank.advance, stackState, firstSelected, lastSelected, same]

end ComplexityOfGenerators.Simulation.WordStack.InputBank
