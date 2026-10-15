import ComplexityOfGenerators.Simulation.CyclicGenerator.Decision
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind

/-! After a successful selection coin, rewind and emit precisely the current
candidate. In particular the empty candidate is accepted without emission. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem output_steps (word : List α) (bits : BitString) (c : Config D)
    (state : c.state = .output) (tape : c.tape 0 = wordTape D word)
    (position : ℕ) (head : c.head 0 = position) (bound : position ≤ word.length)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0)
    (index : c.indexHead ≤ word.length) :
    (bank D).Steps (generatorData word.length) bits c (word.length - position)
      {c with
        head := Function.update c.head 0 (word.length : ℤ)
        output := c.output ++ word.drop position} := by
  generalize remaining_eq : word.length - position = remaining
  induction remaining generalizing position c with
  | zero =>
      have endpoint : position = word.length := by omega
      have heads : Function.update c.head 0 (word.length : ℤ) = c.head := by
        rw [← endpoint, ← head, Function.update_eq_self]
      simpa [heads, endpoint] using
        (TransducerBank.TapeBank.Steps.refl c (B := bank D)
          (data := generatorData word.length) (bits := bits))
  | succ remaining ih =>
      have inside : position < word.length := by omega
      let a := word[position]
      let d : Config D := {c with
        head := Function.update c.head 0 ((position + 1 : ℕ) : ℤ)
        output := c.output ++ [a]}
      have step : (bank D).Steps (generatorData word.length) bits c 1 d := by
        have table : (bank D).instruction (generatorData word.length) c =
            .step .output (c.tape 0 (c.head 0)) .right .stay .stay .stay (some a) := by
          simp [TransducerBank.TapeBank.instruction, bank, state, select, transition,
            head, tape, List.getElem?_eq_getElem inside, a]
        have one := TransducerBank.TapeBank.Steps.single (bank D) _ bits c _ _ _ _ _ _ _ table
        convert one using 1
        apply TransducerBank.BankConfiguration.ext <;>
          simp [d, TransducerBank.TapeBank.advance, bank, state, select, input, auxiliary,
            generatorData, Move.onInput, Nat.min_eq_left index, Move.onInt, head, Function.update_eq_self]
      have tail := ih d state tape (position + 1) (by simp [d]) (by omega)
        input auxiliary index (by omega)
      have joined := step.trans (bank D) tail
      have drop : word.drop position = a :: word.drop (position + 1) := by
        simpa [a] using List.drop_eq_getElem_cons inside
      simpa [d, Function.update_idem, drop, List.append_assoc, Nat.add_comm] using joined

theorem output_executes (word : List α) (bits : BitString) (c : Config D)
    (state : c.state = .outputOrigin) (tape : c.tape 0 = wordTape D word)
    (position : ℕ) (head : c.head 0 = position)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0)
    (index : c.indexHead ≤ word.length) :
    (bank D).Executes (generatorData word.length) bits c
      (position + 1 + word.length) (.accepted (c.output ++ word)) := by
  have rewind := TransducerBank.TapeBank.rewind_steps (bank D) (generatorData word.length) bits
    .outputOrigin .output 0 rfl (by intros; rfl) position c state head
    (by simp [generatorData, input]) (by simp [generatorData, auxiliary]) index
  let d : Config D := {c with state := .output, head := Function.update c.head 0 0}
  have scan := output_steps D word bits d rfl tape 0 (by simp [d]) (Nat.zero_le _) input auxiliary index
  have path := rewind.trans (bank D) scan
  let finish : Config D := {d with
    head := Function.update d.head 0 (word.length : ℤ)
    output := d.output ++ word.drop 0}
  have halted := TransducerBank.TapeBank.Executes.accept (B := bank D)
    (data := generatorData word.length) (bits := bits) finish (by
      simp [TransducerBank.TapeBank.instruction, bank, finish, d, select, transition, tape])
  simpa [finish, d] using path.executes (bank D) halted

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
