import ComplexityOfGenerators.Simulation.LibraryTM.Program

/-! Exact finite schedules for reading all heads and committing one source step. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM

open TransducerBank
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (M : Complexity.TM n) (word : BitString) (bits : BitString)

theorem encoded_go (phase next : State M) (ts : Fin (n + 2) → Complexity.Tape)
    (table : (bank M).instruction (decisionData word) (encoded M word phase ts) =
      .step next (image (ts (select M phase)) (ts (select M phase)).head)
        .stay .stay .stay .stay none) :
    (bank M).Steps (decisionData word) bits (encoded M word phase ts) 1 (encoded M word next ts) :=
  TapeBank.Steps.go (bank M) _ _ _ _ le_rfl (Nat.zero_le _) (Nat.zero_le _) table

theorem encoded_action (phase next : State M) (ts : Fin (n + 2) → Complexity.Tape)
    (j : Fin (n + 2)) (selected : select M phase = j)
    (symbol : Complexity.Γ) (direction : Complexity.Dir3)
    (table : (bank M).instruction (decisionData word) (encoded M word phase ts) =
      .step next (write (decide (((ts j).head : ℤ) = 0)) symbol)
        (move (decide (((ts j).head : ℤ) = 0)) direction) .stay .stay .stay none) :
    (bank M).Steps (decisionData word) bits (encoded M word phase ts) 1
      (encoded M word next (Function.update ts j ((ts j).writeAndMove symbol direction))) := by
  have path := TapeBank.Steps.single (bank M) _ bits _ _ _ _ _ _ _ _ table
  convert path using 1
  apply BankConfiguration.ext
  all_goals simp only [encoded, TapeBank.advance, bank, selected, decisionData, Move.onInput,
    Nat.min_self, Nat.zero_min, Option.toList_none, List.append_nil]
  · funext i
    by_cases same : i = j
    · subst i
      simp only [Function.update_self, writeAndMove_head, move_head]
    · simp [same]
  · funext i
    by_cases same : i = j
    · subst i
      simp only [Function.update_self, Complexity.Tape.writeAndMove, image_move, write_image]
    · simp [same]

theorem gather_steps (q : M.Q) (live : q ≠ M.qhalt)
    (ts : Fin (n + 2) → Complexity.Tape) (markers : ∀ i, (ts i).cells 0 = .start)
    (remaining : ℕ) (j : Fin (n + 3)) (length : j.val + remaining = n + 2)
    (symbols : Fin (n + 2) → Complexity.Γ)
    (cached : ∀ i, i.val < j.val → symbols i = (ts i).read) :
    (bank M).Steps (decisionData word) bits (encoded M word (.gather q j symbols) ts)
      (remaining + 1)
      (encoded M word (.commit (action M q (fun i => (ts i).read)).1 0
        (action M q (fun i => (ts i).read)).2) ts) := by
  induction remaining generalizing j symbols with
  | zero =>
      have full : symbols = fun i => (ts i).read := by
        funext i; exact cached i (by omega)
      subst symbols
      apply encoded_go
      simp [TapeBank.instruction, bank, transition, encoded, live, show ¬j.val < n + 2 by omega]
  | succ remaining ih =>
      have small : j.val < n + 2 := by omega
      let slot : Fin (n + 2) := ⟨j.val, small⟩
      let next : Fin (n + 3) := ⟨j.val + 1, by omega⟩
      let updated := Function.update symbols slot (ts slot).read
      have first : (bank M).Steps (decisionData word) bits
          (encoded M word (.gather q j symbols) ts) 1
          (encoded M word (.gather q next updated) ts) := by
        apply encoded_go
        simp [TapeBank.instruction, bank, transition, encoded, select, live, small,
          slot, next, updated]
        exact congrArg (Function.update symbols slot) (by simpa using read_image (ts slot) (markers slot))
      have tail := ih next (by dsimp [next]; omega) updated (by
        intro i hi
        by_cases same : i = slot
        · subst i; simp [updated]
        · have earlier : i.val < j.val := by
            have different : i.val ≠ j.val := fun h => same (Fin.ext h)
            dsimp [next] at hi; omega
          simpa [updated, same] using cached i earlier)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans (bank M) tail

def committed (ts : Fin (n + 2) → Complexity.Tape)
    (actions : Fin (n + 2) → Complexity.Γ × Complexity.Dir3) (count : ℕ) :
    Fin (n + 2) → Complexity.Tape :=
  fun i => if i.val < count then (ts i).writeAndMove (actions i).1 (actions i).2 else ts i

theorem committed_succ (ts : Fin (n + 2) → Complexity.Tape)
    (actions : Fin (n + 2) → Complexity.Γ × Complexity.Dir3) (j : Fin (n + 2)) :
    Function.update (committed ts actions j.val) j
      (((committed ts actions j.val) j).writeAndMove (actions j).1 (actions j).2) =
      committed ts actions (j.val + 1) := by
  funext i
  by_cases same : i = j
  · subst i; simp [committed]
  · have different : i.val ≠ j.val := fun h => same (Fin.ext h)
    simp only [Function.update_of_ne same, committed]
    simp only [show (i.val < j.val) ↔ (i.val < j.val + 1) by omega]

theorem commit_steps (q : M.Q) (ts : Fin (n + 2) → Complexity.Tape)
    (actions : Fin (n + 2) → Complexity.Γ × Complexity.Dir3)
    (remaining : ℕ) (j : Fin (n + 3)) (length : j.val + remaining = n + 2) :
    (bank M).Steps (decisionData word) bits
      (encoded M word (.commit q j actions) (committed ts actions j.val)) (remaining + 1)
      (encoded M word (ready M q)
        (fun i => (ts i).writeAndMove (actions i).1 (actions i).2)) := by
  induction remaining generalizing j with
  | zero =>
      have full : committed ts actions j.val =
          fun i => (ts i).writeAndMove (actions i).1 (actions i).2 := by
        funext i; simp [committed, show i.val < j.val by omega]
      rw [full]
      apply encoded_go
      simp [TapeBank.instruction, bank, transition, encoded, show ¬j.val < n + 2 by omega]
  | succ remaining ih =>
      have small : j.val < n + 2 := by omega
      let slot : Fin (n + 2) := ⟨j.val, small⟩
      let next : Fin (n + 3) := ⟨j.val + 1, by omega⟩
      have first := encoded_action M word bits (.commit q j actions) (.commit q next actions)
        (committed ts actions j.val) slot (by simp [select, small, slot])
        (actions slot).1 (actions slot).2 (by
          simp [TapeBank.instruction, bank, transition, encoded, select, small, slot, next])
      rw [committed_succ ts actions slot] at first
      have tail := ih next (by dsimp [next]; omega)
      simpa [slot, next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans (bank M) tail

theorem step_schedule (c d : Complexity.Cfg n M.Q) (step : M.step c = some d)
    (markers : ∀ i, (tapes M c i).cells 0 = .start) :
    (bank M).Steps (decisionData word) bits (configuration M word c) (2 * (n + 2) + 2)
      (configuration M word d) := by
  have live := Complexity.TM.state_ne_qhalt_of_step step
  have gather := gather_steps M word bits c.state live (tapes M c) markers (n + 2) 0 (by simp)
    (fun _ => .blank) (by simp)
  have commit := commit_steps M word bits
    (action M c.state (fun i => (tapes M c i).read)).1 (tapes M c)
    (action M c.state (fun i => (tapes M c i).read)).2 (n + 2) 0 (by simp)
  have path := gather.trans (bank M) commit
  simp only [Complexity.TM.step, live, ↓reduceIte, Option.some.injEq] at step
  subst d
  convert path using 1
  · rfl
  · omega
  · unfold configuration
    congr 1
    · simp [action, tapes, -Fin.succ_last]
    · funext i
      refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
      · simp [tapes, action, Complexity.Tape.writeAndMove, write_read, -Fin.succ_last]
      · simp [tapes, action, -Fin.succ_last]
      · simp [tapes, action, -Fin.succ_last]

end ComplexityOfGenerators.Simulation.LibraryTM
