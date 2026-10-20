import ComplexityOfGenerators.Simulation.WordStack.Words

/-! Emit a stored word using only single-letter output instructions. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

def emitWord (src : Fin k) (decode : S → Option O) : Command S O k :=
  .loop src (fun o => o.1.isSome) (.branch src fun o => match o.1 with
    | none => .skip
    | some a => .act src .pop .stay (decode a))

def emitted (src : Fin k) (decode : S → Option O) (m : Memory S O k) : Memory S O k :=
  {m.set src [] with output := m.output ++ (m.store src).filterMap decode}

theorem emitWord_runs (src : Fin k) (decode : S → Option O) {n : ℕ} (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    (emitWord src decode).Runs n bits m (4 * (m.store src).length) (.done (emitted src decode m)) := by
  generalize word_eq : m.store src = word
  induction word generalizing m with
  | nil =>
    have same : m.set src [] = m := by rw [← word_eq, Memory.set_self]
    have final : emitted src decode m = m := by simp [emitted, word_eq, same]
    rw [final]
    exact Runs.loop_stop m src _ _ (by simp [observe, word_eq])
  | cons a word ih =>
    let middle := Program.changeMemory src n .pop .stay (decode a) m
    have head : middle.indexHead = m.indexHead := by
      simp [middle, Program.changeMemory, Move.onInput, Nat.min_eq_left bounded]
    have tail : middle.store src = word := by
      simp [middle, Program.changeMemory, Action.apply, word_eq]
    have body : (Command.branch src fun o => match o.1 with
        | none => Command.skip
        | some a => .act src .pop .stay (decode a)).Runs n bits m 2 (.done middle) := by
      apply Runs.branch m src _ 1 (.done middle)
      simpa only [observe, word_eq, List.head?_cons] using Runs.act m src .pop .stay (decode a)
    have rest := ih middle (by rw [head]; exact bounded) tail
    have final : emitted src decode middle = emitted src decode m := by
      apply Configuration.ext <;>
        simp only [emitted, Memory.set, middle, Program.changeMemory, Action.apply,
          Move.onInput, Nat.min_eq_left bounded, Function.update_idem, Function.update_self,
          word_eq, List.tail_cons]
      cases h : decode a <;> simp [List.filterMap_cons, List.append_assoc, h]
    rw [final] at rest
    have run := Runs.loop m middle src (fun o => o.1.isSome) _ 2 (4 * word.length) _
      (by simp [observe, word_eq]) body rest
    convert run using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

end ComplexityOfGenerators.Simulation.WordStack.Command
