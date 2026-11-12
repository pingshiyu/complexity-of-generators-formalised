import ComplexityOfGenerators.Examples.HAMPATHNative.Cell

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

structure StartState where
  word : List Symbol
  start : ℕ
  seen : Bool
  valid : Bool

def startStep (state : StartState) : StartState :=
  match state.word with
  | .bit false :: rest => ⟨rest, if state.seen then state.start else state.start + 1, state.seen, state.valid⟩
  | .bit true :: rest => ⟨rest, state.start, true, state.valid && !state.seen⟩
  | _ => ⟨state.word.tail, state.start, state.seen, false⟩

def startCode : Local Symbol 32 :=
  (Local.read 2 fun head => match head with
    | some (.bit false) => Local.read 12 fun seen => if seen.isSome then .skip else Local.push 13 (.bit true)
    | some (.bit true) => Local.read 12 fun seen => if seen.isSome then Local.pop 6 else Local.push 12 (.bit true)
    | _ => Local.pop 6).seq (Local.pop 2)

def startEncoded (base : Store) (state : StartState) (clock : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    2 state.word) 6 (flag state.valid)) 12 (flag state.seen)) 13 (List.replicate state.start (.bit true))) 11 clock

theorem startCode_frame (s : Store) (j : Fin 32) (word : j ≠ 2) (valid : j ≠ 6)
    (seen : j ≠ 12) (start : j ≠ 13) : startCode.eval s j = s j := by
  cases phase : s 12 <;> cases head : (s 2).head? with
  | none => simp [startCode, Local.eval, Local.pop, Action.apply, head, phase, word, valid, seen, start]
  | some symbol => cases symbol with
    | separator => simp [startCode, Local.eval, Local.pop, Action.apply, head, phase, word, valid, seen, start]
    | bit value => cases value <;> simp [startCode, Local.eval, Local.pop, Local.push, Action.apply,
        head, phase, word, valid, seen, start]

theorem startCode_eval (base : Store) (state : StartState) (clock : List Symbol) :
    startCode.eval (startEncoded base state clock) = startEncoded base (startStep state) clock := by
  funext j
  by_cases owned : j = 2 ∨ j = 6 ∨ j = 12 ∨ j = 13
  · obtain ⟨word, start, seen, valid⟩ := state
    rcases owned with rfl | rfl | rfl | rfl <;> cases seen <;> cases valid <;>
      cases word with
      | nil => simp [startCode, startEncoded, startStep, flag, Local.eval, Local.pop, Action.apply]
      | cons head rest => cases head with
        | separator => simp [startCode, startEncoded, startStep, flag, Local.eval, Local.pop, Action.apply]
        | bit value => cases value <;> simp [startCode, startEncoded, startStep, flag, Local.eval, Local.pop,
            Local.push, Action.apply, List.replicate_succ]
  · have word : j ≠ 2 := fun equal => owned (Or.inl equal)
    have valid : j ≠ 6 := fun equal => owned (Or.inr (Or.inl equal))
    have seen : j ≠ 12 := fun equal => owned (Or.inr (Or.inr (Or.inl equal)))
    have start : j ≠ 13 := fun equal => owned (Or.inr (Or.inr (Or.inr equal)))
    rw [startCode_frame _ j word valid seen start]
    simp [startEncoded, Function.update_apply, word, valid, seen, start]

theorem startCode_clock (s : Store) : startCode.eval s 11 = s 11 :=
  startCode_frame s 11 (by decide) (by decide) (by decide) (by decide)

theorem startCode_ticks (s : Store) : startCode.ticks s ≤ 6 := by
  cases phase : s 12 <;> cases head : (s 2).head? with
  | none => simp [startCode, Local.ticks, Local.pop, head]
  | some symbol => cases symbol with
    | separator => simp [startCode, Local.ticks, Local.pop, head]
    | bit value => cases value <;> simp [startCode, Local.ticks, Local.pop, Local.push, head, phase]

def startCounted {O : Type} : Routine Symbol O 32 := Routine.counted 11 (Routine.ofLocal startCode)

theorem startCounted_eval {O : Type} (base : Store) (state : StartState) (clock : List Symbol) :
    (startCounted (O := O)).eval (startEncoded base state clock) = startEncoded base (startStep state) clock.tail := by
  simp only [startCounted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop]
  rw [show startEncoded base state clock 11 = clock by simp [startEncoded],
    show Function.update (startEncoded base state clock) 11 clock.tail = startEncoded base state clock.tail by
      simp [startEncoded, Function.update_idem], startCode_eval]

theorem startIterate_eval {O : Type} (base : Store) (state : StartState) (clock : List Symbol) (count : ℕ) :
    (startCounted (O := O)).eval^[count] (startEncoded base state clock) =
      startEncoded base (startStep^[count] state) (clock.drop count) := by
  induction count generalizing state clock with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, startCounted_eval, ih, Function.iterate_succ_apply, List.drop_tail]

def starts {O : Type} : Routine Symbol O 32 := Routine.iterate 11 (Routine.ofLocal startCode) startCode_clock

theorem starts_eval {O : Type} (base : Store) (state : StartState) (count : ℕ) :
    (starts (O := O)).eval (startEncoded base state (List.replicate count (.bit true))) =
      startEncoded base (startStep^[count] state) [] := by
  simpa [starts, Routine.iterate, startEncoded, startCounted] using
    startIterate_eval (O := O) base state (List.replicate count (.bit true)) count

theorem starts_cost {O : Type} (s : Store) : (starts (O := O)).cost s ≤ 10 * (s 11).length := by
  have bounded := Routine.loopCost_bound (startCounted (O := O)).cost (startCounted (O := O)).eval
    (s 11).length 8 s (by
      intro i _
      have cost := startCode_ticks ((Local.pop 11).eval ((startCounted (O := O)).eval^[i] s))
      change 1 + 1 + startCode.ticks ((Local.pop 11).eval ((startCounted (O := O)).eval^[i] s)) ≤ 8
      omega)
  simpa [starts, Routine.iterate, startCounted, Nat.mul_comm] using bounded

end ComplexityOfGenerators.Examples.HAMPATH.Native
