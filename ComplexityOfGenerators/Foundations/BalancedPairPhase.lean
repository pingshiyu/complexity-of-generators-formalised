import ComplexityOfGenerators.Simulation.ClockProgress
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Input

/-! Executable finite-block phase shared by its native implementation and
probability proof. Both source blocks and the selector block are padded. -/

namespace ComplexityOfGenerators.BalancedPairPhase

variable {α : Type}

def cappedCall (M : Machine Unit Bool α) (i time : ℕ) (bits : BitString) : Option (List α) :=
  (M.run (generatorData i) bits time).acceptedWord

def balance (i : ℕ) (first second : Option (List α)) (selector : BitString) : Option (List α) :=
  match first, second with
  | some left, some right =>
      if left.length = i ∧ right.length = i then some left
      else if left.length < i ∧ i < right.length then
        (Simulation.WordStack.RationalSelection.choose (right.length - left.length) (right.length - i) selector).map
          (fun lower => if lower then left else right)
      else if right.length < i ∧ i < left.length then
        (Simulation.WordStack.RationalSelection.choose (left.length - right.length) (left.length - i) selector).map
          (fun lower => if lower then right else left)
      else none
  | _, _ => none

def value (M : Machine Unit Bool α) (i time sourceWidth selectorWidth : ℕ) (bits : BitString) : Option (List α) :=
  balance i (cappedCall M i time (bits.take sourceWidth))
    (cappedCall M i time ((bits.drop sourceWidth).take sourceWidth))
    ((bits.drop (2 * sourceWidth)).take selectorWidth)

theorem cappedCall_eq_some (M : Machine Unit Bool α) (i time : ℕ) (bits : BitString) (word : List α) :
    cappedCall M i time bits = some word ↔ M.run (generatorData i) bits time = .halted (.accepted word) := by
  unfold cappedCall
  cases execution : M.run (generatorData i) bits time with
  | running c => simp [RunState.acceptedWord]
  | halted outcome => cases outcome <;> simp [RunState.acceptedWord, Outcome.acceptedWord]

theorem balance_returns_input (i : ℕ) (first second : Option (List α)) (selector : BitString) (word : List α)
    (accepted : balance i first second selector = some word) : first = some word ∨ second = some word := by
  cases first with
  | none => simp [balance] at accepted
  | some left =>
      cases second with
      | none => simp [balance] at accepted
      | some right =>
          simp only [balance] at accepted
          split_ifs at accepted with equal lower upper
          · exact Or.inl (by simpa using accepted)
          · cases choice : Simulation.WordStack.RationalSelection.choose (right.length - left.length) (right.length - i) selector with
            | none => simp [choice] at accepted
            | some flag => cases flag <;> simp_all
          · cases choice : Simulation.WordStack.RationalSelection.choose (left.length - right.length) (left.length - i) selector with
            | none => simp [choice] at accepted
            | some flag => cases flag <;> simp_all

end ComplexityOfGenerators.BalancedPairPhase
