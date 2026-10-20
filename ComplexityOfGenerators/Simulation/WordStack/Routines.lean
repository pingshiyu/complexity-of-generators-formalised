import ComplexityOfGenerators.Simulation.WordStack.LocalLoop
import ComplexityOfGenerators.Simulation.WordStack.ClearMany

/-! Compositional specifications for deterministic stack subroutines. Every
constructor below supplies an execution proof for primitive commands. -/

namespace ComplexityOfGenerators.Simulation.WordStack

structure Routine (S O : Type) (k : ℕ) where
  command : Command S O k
  eval : Local.Store S k → Local.Store S k
  cost : Local.Store S k → ℕ
  runs : ∀ {n : ℕ} (bits : BitString) (m : Memory S O k), m.indexHead ≤ n →
    ∃ t ≤ cost m.store, command.Runs n bits m t (.done {m with store := eval m.store})

namespace Routine

variable {S O : Type} {k : ℕ}

def seq (a b : Routine S O k) : Routine S O k where
  command := a.command.seq b.command
  eval := fun s => b.eval (a.eval s)
  cost := fun s => a.cost s + 1 + b.cost (a.eval s)
  runs bits m bounded := by
    obtain ⟨s, hs, first⟩ := a.runs bits m bounded
    obtain ⟨t, ht, last⟩ := b.runs bits {m with store := a.eval m.store} bounded
    change t ≤ b.cost (a.eval m.store) at ht
    exact ⟨s + 1 + t, by omega, Command.Runs.seq _ _ _ _ _ _ _ first last⟩

def ofLocal (c : Local S k) : Routine S O k where
  command := c.command
  eval := c.eval
  cost := c.ticks
  runs bits m bounded := ⟨_, le_rfl, c.runs bits m bounded⟩

def skip : Routine S O k := ofLocal .skip

def clear (j : Fin k) : Routine S O k where
  command := Command.clear j
  eval := fun s => Function.update s j []
  cost := fun s => 3 * (s j).length
  runs bits m bounded := ⟨_, le_rfl, Command.clear_runs j bits m bounded⟩

def transfer (src dst : Fin k) (different : src ≠ dst) (f : S → S) : Routine S O k where
  command := Command.transfer src dst f
  eval := fun s => Function.update (Function.update s src []) dst ((s src).reverse.map f ++ s dst)
  cost := fun s => 6 * (s src).length
  runs bits m bounded := ⟨_, le_rfl, Command.transfer_runs src dst different f bits m bounded⟩

/-- Clear the scratch stack before copying, so this subroutine is total on
arbitrary caller memories. -/
def copy (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch) (dt : dst ≠ scratch)
    (f : S → S) : Routine S O k where
  command := (Command.clear scratch).seq (Command.copy src dst scratch f)
  eval := fun s => Function.update (Function.update s scratch []) dst ((s src).map f ++ s dst)
  cost := fun s => 3 * (s scratch).length + 14 * (s src).length + 2
  runs bits m bounded := by
    have first := Command.clear_runs scratch bits m bounded
    have last := Command.copy_runs src dst scratch sd st dt f bits (m.set scratch []) bounded (by simp)
    simp only [Memory.set_there _ _ st, Memory.set_there _ _ dt] at last
    refine ⟨3 * (m.store scratch).length + 1 + (14 * (m.store src).length + 1), by omega, ?_⟩
    exact Command.Runs.seq _ _ _ _ _ _ _ first last

def assign (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch) (dt : dst ≠ scratch)
    (f : S → S) : Routine S O k := (clear dst).seq (copy src dst scratch sd st dt f)

@[simp] theorem assign_eval (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch)
    (dt : dst ≠ scratch) (f : S → S) (s : Local.Store S k) :
    (assign (O := O) src dst scratch sd st dt f).eval s =
      Function.update (Function.update s scratch []) dst ((s src).map f) := by
  funext j
  by_cases hd : j = dst <;> by_cases ht : j = scratch <;>
    simp [assign, seq, clear, copy, Function.update_apply, sd, dt, hd, ht]

@[simp] theorem assign_cost (src dst scratch : Fin k) (sd : src ≠ dst) (st : src ≠ scratch)
    (dt : dst ≠ scratch) (f : S → S) (s : Local.Store S k) :
    (assign (O := O) src dst scratch sd st dt f).cost s =
      3 * (s dst).length + 3 * (s scratch).length + 14 * (s src).length + 3 := by
  simp [assign, seq, clear, copy, sd, dt.symm]
  ring

def clearMany (registers : List (Fin k)) : Routine S O k :=
  registers.foldr (fun j rest => (clear j).seq rest) skip

@[simp] theorem clearMany_eval (registers : List (Fin k)) (s : Local.Store S k) :
    (clearMany (O := O) registers).eval s = fun j => if j ∈ registers then [] else s j := by
  induction registers generalizing s with
  | nil => simp [clearMany, skip, ofLocal, Local.eval]
  | cons j rest ih =>
    change (clearMany rest).eval (Function.update s j []) = _
    rw [ih]
    funext i
    by_cases equal : i = j <;> by_cases member : i ∈ rest <;> simp [equal, member]

theorem clearMany_cost (registers : List (Fin k)) (s : Local.Store S k) (budget : ℕ)
    (sizes : ∀ j ∈ registers, (s j).length ≤ budget) :
    (clearMany (O := O) registers).cost s ≤ registers.length * (3 * budget + 1) := by
  induction registers generalizing s with
  | nil => simp [clearMany, skip, ofLocal, Local.ticks]
  | cons j rest ih =>
    have bound := sizes j (by simp)
    have tail := ih (Function.update s j []) (by
      intro i member
      by_cases equal : i = j
      · simp [equal]
      · simpa [equal] using sizes i (by simp [member]))
    change 3 * (s j).length + 1 + (clearMany rest).cost (Function.update s j []) ≤ _
    simp only [List.length_cons]
    nlinarith

noncomputable def clocked [Fintype S] (clock : Fin k) (body : Local S k)
    (frame : ∀ s, body.eval s clock = s clock) : Routine S O k where
  command := Local.clocked clock body
  eval := fun s => (Local.counted clock body).eval^[(s clock).length] s
  cost := fun s => (s clock).length * (body.bound + 4)
  runs bits m bounded := by
    obtain ⟨t, cost, run, _⟩ := Local.repeat_runs clock body frame bits m bounded
    refine ⟨t, cost, ?_⟩
    have equal (count : ℕ) :
        (Local.counted clock body).apply^[count] m =
          {m with store := (Local.counted clock body).eval^[count] m.store} := by
      induction count with
      | zero => rfl
      | succ count ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        rfl
    simpa only [equal] using run

end Routine
end ComplexityOfGenerators.Simulation.WordStack
