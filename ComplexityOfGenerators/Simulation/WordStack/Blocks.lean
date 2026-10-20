import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops
import ComplexityOfGenerators.Simulation.WordStack.LocalZipper

/-! Split a fixed-size prefix from a stored random tape. The extracted block is
reversed, ready for the source-call setup routine. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Blocks

variable {S O : Type} {k : ℕ}

def body (src dst : Fin k) : Routine S O k := Routine.ofLocal (Local.moveOne src dst none)

theorem body_frame (src dst : Fin k) (j : Fin k) (js : j ≠ src) (jd : j ≠ dst) (s : Local.Store S k) :
    (body (O := O) src dst).eval s j = s j := by
  cases h : s src <;> simp [body, Routine.ofLocal, Local.moveOne, Local.eval, Local.pop, Local.push,
    Action.apply, h, js, jd]

def routine (counter src dst : Fin k) (cs : counter ≠ src) (cd : counter ≠ dst) : Routine S O k :=
  Routine.iterate counter (body src dst) (body_frame src dst counter cs cd)

def taken (counter src dst : Fin k) (s : Local.Store S k) (count : ℕ) : Local.Store S k :=
  Function.update (Function.update (Function.update s counter ((s counter).drop count)) src ((s src).drop count))
    dst (((s src).take count).reverse ++ s dst)

theorem step_taken (counter src dst : Fin k) (cs : counter ≠ src) (cd : counter ≠ dst) (sd : src ≠ dst)
    (s : Local.Store S k) (count : ℕ) :
    taken counter src dst ((Routine.counted counter (body (O := O) src dst)).eval s) count =
      taken counter src dst s (count + 1) := by
  have sc := cs.symm
  have dc := cd.symm
  have ds := sd.symm
  cases h : s src <;> funext j <;>
    by_cases hc : j = counter <;> by_cases hs : j = src <;> by_cases hd : j = dst <;>
      simp_all [taken, Routine.counted, Routine.seq, Routine.ofLocal, body,
        Local.moveOne, Local.eval, Local.pop, Local.push, Action.apply, Function.update_apply,
        List.drop_tail, List.reverse_cons, List.append_assoc]

theorem iterate_taken (counter src dst : Fin k) (cs : counter ≠ src) (cd : counter ≠ dst) (sd : src ≠ dst)
    (s : Local.Store S k) (count : ℕ) :
    (Routine.counted counter (body (O := O) src dst)).eval^[count] s = taken counter src dst s count := by
  induction count generalizing s with
  | zero => simp [taken, Function.update_eq_self]
  | succ count ih =>
    rw [Function.iterate_succ_apply, ih, step_taken counter src dst cs cd sd]

theorem routine_eval (counter src dst : Fin k) (cs : counter ≠ src) (cd : counter ≠ dst) (sd : src ≠ dst)
    (s : Local.Store S k) :
    (routine (O := O) counter src dst cs cd).eval s =
      Function.update (Function.update (Function.update s counter []) src ((s src).drop (s counter).length))
        dst (((s src).take (s counter).length).reverse ++ s dst) := by
  simp only [routine, Routine.iterate, iterate_taken counter src dst cs cd sd, taken, List.drop_length]

theorem body_cost (src dst : Fin k) (s : Local.Store S k) : (body (O := O) src dst).cost s ≤ 4 := by
  cases h : s src <;> simp [body, Routine.ofLocal, Local.moveOne, Local.ticks, h, Local.pop, Local.push]

theorem routine_cost (counter src dst : Fin k) (cs : counter ≠ src) (cd : counter ≠ dst)
    (s : Local.Store S k) : (routine (O := O) counter src dst cs cd).cost s ≤ 8 * (s counter).length := by
  change Routine.loopCost _ _ _ _ ≤ _
  apply (Routine.loopCost_bound _ _ _ 6 s ?_).trans (by omega)
  intro i hi
  simp only [Routine.counted, Routine.seq, Routine.ofLocal, Local.pop, Local.ticks]
  exact Nat.add_le_add_left (body_cost (O := O) src dst _) 2

end ComplexityOfGenerators.Simulation.WordStack.Blocks
