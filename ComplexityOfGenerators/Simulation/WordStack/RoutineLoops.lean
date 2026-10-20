import ComplexityOfGenerators.Simulation.WordStack.Routines

/-! Conditionals and clocked loops of verified deterministic subroutines. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Routine

variable {S O : Type} {k : ℕ}

def branch (j : Fin k) (next : Option S → Routine S O k) : Routine S O k where
  command := .branch j (fun o => (next o.1).command)
  eval := fun s => (next (s j).head?).eval s
  cost := fun s => 1 + (next (s j).head?).cost s
  runs bits m bounded := by
    obtain ⟨t, ht, run⟩ := (next (m.store j).head?).runs bits m bounded
    exact ⟨1 + t, by omega, Command.Runs.branch _ _ _ _ _ run⟩

def apply (c : Routine S O k) (m : Memory S O k) : Memory S O k := {m with store := c.eval m.store}

def loopCost (cost : Local.Store S k → ℕ) (f : Local.Store S k → Local.Store S k) : ℕ → Local.Store S k → ℕ
  | 0, _ => 0
  | n + 1, s => cost s + 2 + loopCost cost f n (f s)

theorem loopCost_bound (cost : Local.Store S k → ℕ) (f : Local.Store S k → Local.Store S k)
    (n budget : ℕ) (s : Local.Store S k)
    (bounded : ∀ i < n, cost (f^[i] s) ≤ budget) : loopCost cost f n s ≤ n * (budget + 2) := by
  induction n generalizing s with
  | zero => simp [loopCost]
  | succ n ih =>
    have first := bounded 0 (by omega)
    have rest := ih (f s) (by
      intro i hi
      simpa only [Function.iterate_succ_apply] using bounded (i + 1) (by omega))
    simp only [loopCost, Function.iterate_zero, id_eq] at *
    nlinarith

def counted (clock : Fin k) (body : Routine S O k) : Routine S O k :=
  (ofLocal (Local.pop clock)).seq body

theorem counted_clock (clock : Fin k) (body : Routine S O k)
    (frame : ∀ s, body.eval s clock = s clock) (s : Local.Store S k) :
    (counted clock body).eval s clock = (s clock).tail := by
  simp [counted, seq, ofLocal, Local.eval_pop, frame]

theorem iterate_runs (clock : Fin k) (body : Routine S O k)
    (frame : ∀ s, body.eval s clock = s clock) {n : ℕ} (bits : BitString)
    (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    ∃ t ≤ loopCost (counted clock body).cost (counted clock body).eval (m.store clock).length m.store,
      (Command.loop clock (fun o => o.1.isSome) (counted clock body).command).Runs n bits m t
        (.done {m with store := (counted clock body).eval^[(m.store clock).length] m.store}) := by
  generalize equation : m.store clock = word
  induction word generalizing m with
  | nil =>
    exact ⟨0, le_rfl, Command.Runs.loop_stop m clock _ _ (by simp [observe, equation])⟩
  | cons a word ih =>
    let middle : Memory S O k := {m with store := (counted clock body).eval m.store}
    have clock_eq : middle.store clock = word := by
      simp only [middle, counted_clock clock body frame, equation, List.tail_cons]
    obtain ⟨s, cost, first⟩ := (counted clock body).runs bits m bounded
    obtain ⟨t, cost', rest⟩ := ih middle bounded clock_eq
    refine ⟨1 + s + 1 + t, ?_, ?_⟩
    · change t ≤ loopCost (counted clock body).cost (counted clock body).eval word.length
        ((counted clock body).eval m.store) at cost'
      simp only [List.length_cons, loopCost]
      omega
    · have run := Command.Runs.loop m middle clock (fun o => o.1.isSome) (counted clock body).command
        s t _ (by simp [observe, equation]) first rest
      simpa only [middle, List.length_cons, Function.iterate_succ_apply] using run

def iterate (clock : Fin k) (body : Routine S O k)
    (frame : ∀ s, body.eval s clock = s clock) : Routine S O k where
  command := .loop clock (fun o => o.1.isSome) (counted clock body).command
  eval := fun s => (counted clock body).eval^[(s clock).length] s
  cost := fun s => loopCost (counted clock body).cost (counted clock body).eval (s clock).length s
  runs bits m bounded := iterate_runs clock body frame bits m bounded

theorem iterate_clock (clock : Fin k) (body : Routine S O k)
    (frame : ∀ s, body.eval s clock = s clock) (s : Local.Store S k) :
    (iterate clock body frame).eval s clock = [] := by
  have tail (t : ℕ) (store : Local.Store S k) :
      ((counted clock body).eval^[t] store) clock = (store clock).drop t := by
    induction t generalizing store with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply, ih, counted_clock clock body frame]
      exact List.drop_tail
  simpa only [iterate, List.drop_length] using tail (s clock).length s

theorem iterate_frame (clock : Fin k) (body : Routine S O k)
    (frame : ∀ s, body.eval s clock = s clock) (j : Fin k) (different : j ≠ clock)
    (fixed : ∀ s, body.eval s j = s j) (s : Local.Store S k) :
    (iterate clock body frame).eval s j = s j := by
  have step (store : Local.Store S k) : (counted clock body).eval store j = store j := by
    simp [counted, seq, ofLocal, fixed, different]
  have iter (t : ℕ) : ((counted clock body).eval^[t] s) j = s j := by
    induction t with
    | zero => rfl
    | succ t ih => simpa only [Function.iterate_succ_apply', step] using ih
  exact iter _

end ComplexityOfGenerators.Simulation.WordStack.Routine
