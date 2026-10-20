import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops

namespace ComplexityOfGenerators.Simulation.WordStack.DrainPair

variable {S O : Type} {k : ℕ}

def body (first second : Fin k) : Local S k :=
  .read first fun head => if head.isSome then Local.pop first else Local.pop second

theorem body_frame (first second j : Fin k) (jf : j ≠ first) (js : j ≠ second) (s : Local.Store S k) :
    (body first second).eval s j = s j := by
  cases h : s first <;> simp [body, Local.eval_read, h, jf, js]

def routine (counter first second : Fin k) (cf : counter ≠ first) (cs : counter ≠ second) : Routine S O k :=
  Routine.iterate counter (Routine.ofLocal (body first second)) (body_frame first second counter cf cs)

def drained (counter first second : Fin k) (s : Local.Store S k) (count : ℕ) : Local.Store S k :=
  Function.update (Function.update (Function.update s counter ((s counter).drop count))
    first ((s first).drop count)) second ((s second).drop (count - (s first).length))

theorem step_drained (counter first second : Fin k) (cf : counter ≠ first) (cs : counter ≠ second)
    (fs : first ≠ second) (s : Local.Store S k) (count : ℕ) :
    drained counter first second
        ((Routine.counted counter (Routine.ofLocal (O := O) (body first second))).eval s) count =
      drained counter first second s (count + 1) := by
  have fc := cf.symm
  have sc := cs.symm
  have sf := fs.symm
  cases h : s first <;> funext j <;>
    by_cases hc : j = counter <;> by_cases hf : j = first <;> by_cases hs : j = second <;>
      simp_all [drained, Routine.counted, Routine.seq, Routine.ofLocal, body,
        Local.eval, Local.pop, Action.apply, Function.update_apply, List.drop_tail,
        Nat.add_sub_add_right]

theorem iterate_drained (counter first second : Fin k) (cf : counter ≠ first) (cs : counter ≠ second)
    (fs : first ≠ second) (s : Local.Store S k) (count : ℕ) :
    (Routine.counted counter (Routine.ofLocal (O := O) (body first second))).eval^[count] s =
      drained counter first second s count := by
  induction count generalizing s with
  | zero => simp [drained, Function.update_eq_self]
  | succ count ih => rw [Function.iterate_succ_apply, ih, step_drained counter first second cf cs fs]

theorem routine_eval (counter first second : Fin k) (cf : counter ≠ first) (cs : counter ≠ second)
    (fs : first ≠ second) (s : Local.Store S k) :
    (routine (O := O) counter first second cf cs).eval s =
      Function.update (Function.update (Function.update s counter []) first ((s first).drop (s counter).length))
        second ((s second).drop ((s counter).length - (s first).length)) := by
  simp only [routine, Routine.iterate, iterate_drained counter first second cf cs fs, drained, List.drop_length]

theorem body_ticks (first second : Fin k) (s : Local.Store S k) : (body first second).ticks s = 2 := by
  cases h : s first <;> simp [body, Local.ticks, Local.pop, h]

theorem routine_cost (counter first second : Fin k) (cf : counter ≠ first) (cs : counter ≠ second)
    (s : Local.Store S k) : (routine (O := O) counter first second cf cs).cost s ≤ 6 * (s counter).length := by
  change Routine.loopCost _ _ _ _ ≤ _
  apply (Routine.loopCost_bound _ _ _ 4 s ?_).trans (by omega)
  intro i hi
  simp [Routine.counted, Routine.seq, Routine.ofLocal, Local.pop, Local.ticks, body_ticks]

end ComplexityOfGenerators.Simulation.WordStack.DrainPair
