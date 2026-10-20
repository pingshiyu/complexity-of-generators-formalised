import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops

namespace ComplexityOfGenerators.Simulation.WordStack.Routine

variable {S O : Type} {k : ℕ}

def Fixes (c : Routine S O k) (j : Fin k) : Prop := ∀ s, c.eval s j = s j

theorem Fixes.seq {a b : Routine S O k} {j : Fin k} (ha : a.Fixes j) (hb : b.Fixes j) :
    (a.seq b).Fixes j := fun s => (hb _).trans (ha s)

theorem Fixes.branch (reg : Fin k) (next : Option S → Routine S O k) (j : Fin k)
    (fixed : ∀ head, (next head).Fixes j) : (branch reg next).Fixes j := fun s => fixed _ s

@[simp] theorem fixes_skip (j : Fin k) : (skip : Routine S O k).Fixes j := fun _ => rfl

theorem fixes_clear (reg j : Fin k) (different : j ≠ reg) : (clear (S := S) (O := O) reg).Fixes j := by
  intro s
  exact Function.update_of_ne different ..

theorem fixes_push (reg j : Fin k) (a : S) (different : j ≠ reg) :
    (ofLocal (O := O) (Local.push reg a)).Fixes j := by
  intro s
  exact Function.update_of_ne different ..

theorem fixes_pop (reg j : Fin k) (different : j ≠ reg) :
    (ofLocal (S := S) (O := O) (Local.pop reg)).Fixes j := by
  intro s
  exact Function.update_of_ne different ..

theorem fixes_assign (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch)
    (dt : dst ≠ scratch) (f : S → S) (j : Fin k) (jd : j ≠ dst) (jt : j ≠ scratch) :
    (assign (O := O) src dst scratch sd st dt f).Fixes j := by
  intro s
  simp [assign_eval, jd, jt]

theorem fixes_transfer (src dst : Fin k) (sd : src ≠ dst) (f : S → S) (j : Fin k)
    (js : j ≠ src) (jd : j ≠ dst) : (transfer (O := O) src dst sd f).Fixes j := by
  intro s
  simp [transfer, js, jd]

theorem Fixes.iterate (clock : Fin k) (body : Routine S O k) (frame : body.Fixes clock)
    (j : Fin k) (different : j ≠ clock) (fixed : body.Fixes j) :
    (iterate clock body frame).Fixes j := iterate_frame clock body frame j different fixed

end ComplexityOfGenerators.Simulation.WordStack.Routine
