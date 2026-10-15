import ComplexityOfGenerators.Simulation.CyclicGenerator.Decision
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind

/-! Erase and reuse the decider's visited work interval. The eraser scans to
the first untouched cell on the left, clears the interval to the right, then
returns to the origin. Its workspace depends on the interval, not on how many
candidate words have already been tested. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

def intervalTape (lo hi : ℤ) (work : ℤ → Option (Fin D.symbols)) (i : ℤ) : Symbol D :=
  if lo ≤ i ∧ i ≤ hi then {work := work i, touched := true} else {}

theorem intervalTape_clear (lo hi : ℤ) (work : ℤ → Option (Fin D.symbols)) :
    Function.update (intervalTape D lo hi work) lo {} = intervalTape D (lo + 1) hi work := by
  funext i
  by_cases same : i = lo
  · subst i
    simp [intervalTape]
  · simp only [Function.update_of_ne same, intervalTape]
    split_ifs <;> first | rfl | omega

theorem eraseLeft_steps (n : ℕ) (bits : BitString) (seen : Bool)
    (lo hi : ℤ) (work : ℤ → Option (Fin D.symbols)) (distance : ℕ) (c : Config D)
    (state : c.state = .eraseLeft seen) (head : c.head 1 = lo + distance)
    (upper : lo + distance ≤ hi) (tape : c.tape 1 = intervalTape D lo hi work)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0) (index : c.indexHead ≤ n) :
    (bank D).Steps (generatorData n) bits c (distance + 2)
      {c with state := .eraseRight seen, head := Function.update c.head 1 lo} := by
  induction distance generalizing c with
  | zero =>
      simp only [Nat.cast_zero, add_zero] at upper
      let d : Config D := {c with head := Function.update c.head 1 (lo - 1)}
      have left : (bank D).Steps (generatorData n) bits c 1 d := by
        have one := TransducerBank.TapeBank.Steps.read (bank D) (generatorData n) bits c
          (.eraseLeft seen) .left 1 (by simp [bank, state, select])
          (by simp [input, generatorData]) (by simp [auxiliary, generatorData]) index (by
            simp [TransducerBank.TapeBank.instruction, bank, state, select, transition, head,
              tape, intervalTape, upper])
        simpa [d, state, head, Move.onInt] using one
      have right : (bank D).Steps (generatorData n) bits d 1
          {c with state := .eraseRight seen, head := Function.update c.head 1 lo} := by
        have one := TransducerBank.TapeBank.Steps.read (bank D) (generatorData n) bits d
          (.eraseRight seen) .right 1 (by simp [bank, d, state, select])
          (by simp [d, input, generatorData]) (by simp [d, auxiliary, generatorData]) index (by
            simp [TransducerBank.TapeBank.instruction, bank, d, state, select, transition,
              tape, intervalTape])
        simpa [d, Function.update_idem, Move.onInt] using one
      exact left.trans (bank D) right
  | succ distance ih =>
      simp only [Nat.cast_add, Nat.cast_one] at upper
      have positive : (0 : ℤ) ≤ (distance : ℤ) + 1 := by omega
      let d : Config D := {c with head := Function.update c.head 1 (lo + distance)}
      have left : (bank D).Steps (generatorData n) bits c 1 d := by
        have one := TransducerBank.TapeBank.Steps.read (bank D) (generatorData n) bits c
          (.eraseLeft seen) .left 1 (by simp [bank, state, select])
          (by simp [input, generatorData]) (by simp [auxiliary, generatorData]) index (by
            simp [TransducerBank.TapeBank.instruction, bank, state, select, transition, head,
              tape, intervalTape, upper, positive])
        convert one using 1
        simp [d, state, head, Move.onInt, add_sub_assoc]
      have rest := ih d state (by simp [d]) (by omega) tape input auxiliary index
      simpa [d, Function.update_idem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        left.trans (bank D) rest

theorem eraseRight_steps (n : ℕ) (bits : BitString) (seen : Bool)
    (hi : ℤ) (work : ℤ → Option (Fin D.symbols)) (width : ℕ) (lo : ℤ) (c : Config D)
    (state : c.state = .eraseRight seen) (head : c.head 1 = lo)
    (size : hi + 1 = lo + width) (tape : c.tape 1 = intervalTape D lo hi work)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0) (index : c.indexHead ≤ n) :
    (bank D).Steps (generatorData n) bits c (width + 1)
      {c with
        state := .workOrigin seen
        head := Function.update c.head 1 hi
        tape := Function.update c.tape 1 (fun _ => {})} := by
  induction width generalizing lo c with
  | zero =>
      have empty : c.tape 1 = fun _ => ({} : Symbol D) := by
        rw [tape]
        funext i
        simp only [intervalTape]
        rw [if_neg (by omega)]
      have one := TransducerBank.TapeBank.Steps.read (bank D) (generatorData n) bits c
        (.workOrigin seen) .left 1 (by simp [bank, state, select])
        (by simp [input, generatorData]) (by simp [auxiliary, generatorData]) index (by
          simp [TransducerBank.TapeBank.instruction, bank, state, select, transition, empty])
      have sameHead : lo - 1 = hi := by omega
      simpa [Move.onInt, head, sameHead, ← empty, Function.update_eq_self] using one
  | succ width ih =>
      have inside : lo ≤ hi := by omega
      let d : Config D := {c with
        head := Function.update c.head 1 (lo + 1)
        tape := Function.update c.tape 1 (intervalTape D (lo + 1) hi work)}
      have one : (bank D).Steps (generatorData n) bits c 1 d := by
        have table : (bank D).instruction (generatorData n) c =
            .step (.eraseRight seen) {} .right .stay .stay .stay none := by
          simp [TransducerBank.TapeBank.instruction, bank, state, select, transition, head,
            tape, intervalTape, inside]
        have step := TransducerBank.TapeBank.Steps.single (bank D) _ bits c _ _ _ _ _ _ _ table
        convert step using 1
        apply TransducerBank.BankConfiguration.ext <;>
          simp [d, state, TransducerBank.TapeBank.advance, bank, select, head, tape,
            intervalTape_clear, input, auxiliary, generatorData, Move.onInput,
            Nat.min_eq_left index, Move.onInt]
      have rest := ih (lo + 1) d state (by simp [d]) (by omega) (by simp [d])
        input auxiliary index
      simpa [d, Function.update_idem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        one.trans (bank D) rest

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
