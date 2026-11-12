import ComplexityOfGenerators.Simulation.WordStack.Output

/-! Compile a fixed output word into single-letter finite-control instructions. -/
namespace ComplexityOfGenerators.Simulation.WordStack.Command
variable {S O : Type} {k : ℕ}

def emitFixed (register : Fin k) : List O → Command S O k
  | [] => .skip
  | symbol :: rest => (Command.act register .stay .stay (some symbol)).seq (emitFixed register rest)

theorem emitFixed_runs (register : Fin k) (word : List O) {n : ℕ} (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (emitFixed register word).Runs n bits m (2 * word.length) (.done {m with output := m.output ++ word}) := by
  induction word generalizing m with
  | nil => simpa [emitFixed] using Runs.skip m
  | cons symbol rest ih =>
    let middle : Memory S O k := {m with output := m.output ++ [symbol]}
    have first : (Command.act register .stay .stay (some symbol)).Runs n bits m 1 (.done middle) := by
      simpa [middle, Program.changeMemory, Action.apply, Move.onInput, Nat.min_eq_left bounded,
        Function.update_eq_self] using Runs.act m register .stay .stay (some symbol) (n := n) (bits := bits)
    have last := ih middle bounded
    have run := Runs.seq _ _ _ _ _ _ _ first last
    simpa [emitFixed, middle, List.length_cons, List.append_assoc, Nat.mul_add, Nat.add_comm] using run

end ComplexityOfGenerators.Simulation.WordStack.Command
