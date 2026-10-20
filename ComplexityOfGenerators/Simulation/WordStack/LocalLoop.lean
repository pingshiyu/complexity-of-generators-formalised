import ComplexityOfGenerators.Simulation.WordStack.Local

/-! A unary clock controls repeated executions of a finite local routine. -/

namespace ComplexityOfGenerators.Simulation.WordStack

namespace Local

variable {S O : Type} {k : ℕ}

def counted (clock : Fin k) (body : Local S k) : Local S k := (pop clock).seq body

def clocked (clock : Fin k) (body : Local S k) : Command S O k :=
  .loop clock (fun o => o.1.isSome) (counted clock body).command

theorem repeat_runs [Fintype S] (clock : Fin k) (body : Local S k)
    (frame : ∀ s, body.eval s clock = s clock) {n : ℕ} (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    ∃ t ≤ (m.store clock).length * (body.bound + 4),
      (clocked clock body).Runs n bits m t
        (.done ((counted clock body).apply^[(m.store clock).length] m)) ∧
      (((counted clock body).apply^[(m.store clock).length] m).store clock = []) := by
  generalize equation : m.store clock = word
  induction word generalizing m with
  | nil =>
    exact ⟨0, by simp, Command.Runs.loop_stop m clock _ _ (by simp [observe, equation]), equation⟩
  | cons a word ih =>
    let middle := (counted clock body).apply m
    have clock_eq : middle.store clock = word := by
      simp [middle, counted, eval_seq, frame, equation]
    obtain ⟨t, cost, rest, final⟩ := ih middle (by simpa [middle] using bounded) clock_eq
    have run := Command.Runs.loop m middle clock (fun o => o.1.isSome) (counted clock body).command
      ((counted clock body).ticks m.store) t _ (by simp [observe, equation])
      ((counted clock body).runs bits m bounded) rest
    refine ⟨1 + (counted clock body).ticks m.store + 1 + t, ?_, ?_, ?_⟩
    · have step := body.ticks_le ((pop clock).eval m.store)
      simp only [counted, ticks, pop] at *
      simp only [List.length_cons]
      nlinarith
    · simpa only [clocked, List.length_cons, Function.iterate_succ_apply] using run
    · simpa only [List.length_cons, Function.iterate_succ_apply] using final

end Local
end ComplexityOfGenerators.Simulation.WordStack
