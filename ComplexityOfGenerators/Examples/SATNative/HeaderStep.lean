import ComplexityOfGenerators.Examples.SATHeader
import ComplexityOfGenerators.Simulation.WordStack.TransferWhile
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 16

structure ScanState where
  word : List Symbol
  count : ℕ
  ones : Bool
  valid : Bool

def step (state : ScanState) : ScanState :=
  match state.word with
  | .one :: rest => ⟨rest, if state.ones then state.count + 1 else state.count,
      state.ones, state.valid && state.ones⟩
  | .zero :: rest => ⟨rest, state.count, false, state.valid⟩
  | _ => ⟨state.word.tail, state.count, false, false⟩

/-- One active-count field symbol is consumed per primitive local iteration.
Late unary marks, nonbinary symbols and missing symbols clear validity. -/
def scanCode : Local Symbol 16 :=
  (Local.read 2 fun head => match head with
    | some .one => Local.read 8 fun phase => if phase.isSome then Local.push 5 .one else Local.pop 6
    | some .zero => Local.pop 8
    | _ => (Local.pop 6).seq (Local.pop 8)).seq (Local.pop 2)

def encoded (base : Store) (state : ScanState) (clock : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    2 state.word) 5 (List.replicate state.count .one))
    6 (if state.valid then [.one] else [])) 8 (if state.ones then [.one] else [])) 7 clock

theorem scanCode_frame (s : Store) (j : Fin 16) (word : j ≠ 2) (count : j ≠ 5)
    (valid : j ≠ 6) (phase : j ≠ 8) : scanCode.eval s j = s j := by
  cases head : (s 2).head? with
  | none => simp [scanCode, Local.eval, Local.pop, Action.apply, head, word, valid, phase]
  | some symbol =>
    cases symbol <;> simp [scanCode, Local.eval, Local.pop, Local.push, Action.apply,
      head, word, valid, phase]
    split <;> simp [Local.eval, count, valid]

theorem scanCode_eval (base : Store) (state : ScanState) (clock : List Symbol) :
    scanCode.eval (encoded base state clock) = encoded base (step state) clock := by
  funext j
  by_cases owned : j = 2 ∨ j = 5 ∨ j = 6 ∨ j = 8
  · obtain ⟨word, count, ones, valid⟩ := state
    rcases owned with rfl | rfl | rfl | rfl <;>
      cases word with
      | nil => cases ones <;> cases valid <;>
          simp [scanCode, encoded, step, Local.eval, Local.push, Local.pop, Action.apply]
      | cons head rest => cases head <;> cases ones <;> cases valid <;>
          simp [scanCode, encoded, step, Local.eval, Local.push, Local.pop, Action.apply, List.replicate_succ]
  · have word : j ≠ 2 := fun equal => owned (Or.inl equal)
    have count : j ≠ 5 := fun equal => owned (Or.inr (Or.inl equal))
    have valid : j ≠ 6 := fun equal => owned (Or.inr (Or.inr (Or.inl equal)))
    have phase : j ≠ 8 := fun equal => owned (Or.inr (Or.inr (Or.inr equal)))
    rw [scanCode_frame _ j word count valid phase]
    simp [encoded, Function.update_apply, word, count, valid, phase]

theorem scanCode_clock (s : Store) : scanCode.eval s 7 = s 7 := by
  exact scanCode_frame s 7 (by decide) (by decide) (by decide) (by decide)

theorem scanCode_ticks (s : Store) : scanCode.ticks s ≤ 6 := by
  cases head : (s 2).head? with
  | none => simp [scanCode, Local.ticks, Local.pop, head]
  | some symbol =>
    cases symbol <;> simp [scanCode, Local.ticks, Local.pop, Local.push, head]
    (try split) <;> (try simp [Local.ticks])

def scanCounted {O : Type} : Routine Symbol O 16 := Routine.counted 7 (Routine.ofLocal scanCode)

theorem encoded_clock (base : Store) (state : ScanState) (clock : List Symbol) :
    Function.update (encoded base state clock) 7 clock.tail = encoded base state clock.tail := by
  simp [encoded, Function.update_idem]

theorem scanCounted_eval {O : Type} (base : Store) (state : ScanState) (clock : List Symbol) :
    (scanCounted (O := O)).eval (encoded base state clock) = encoded base (step state) clock.tail := by
  simp only [scanCounted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop]
  rw [show encoded base state clock 7 = clock by simp [encoded], encoded_clock, scanCode_eval]

theorem scanIterate_eval {O : Type} (base : Store) (state : ScanState) (clock : List Symbol) (steps : ℕ) :
    (scanCounted (O := O)).eval^[steps] (encoded base state clock) =
      encoded base (step^[steps] state) (clock.drop steps) := by
  induction steps generalizing state clock with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply, scanCounted_eval, ih, Function.iterate_succ_apply]
    rw [List.drop_tail]

def scanRoutine {O : Type} : Routine Symbol O 16 :=
  Routine.iterate 7 (Routine.ofLocal scanCode) scanCode_clock

theorem scanRoutine_eval {O : Type} (base : Store) (state : ScanState) (count : ℕ) :
    (scanRoutine (O := O)).eval (encoded base state (List.replicate count .one)) =
      encoded base (step^[count] state) [] := by
  have execution := scanIterate_eval (O := O) base state (List.replicate count .one) count
  simpa [scanRoutine, Routine.iterate, encoded, scanCounted] using execution

theorem scanRoutine_cost {O : Type} (s : Store) : (scanRoutine (O := O)).cost s ≤ 10 * (s 7).length := by
  have bounded := Routine.loopCost_bound (scanCounted (O := O)).cost (scanCounted (O := O)).eval
    (s 7).length 8 s (by
      intro i _
      have cost := scanCode_ticks (Local.pop 7 |>.eval ((scanCounted (O := O)).eval^[i] s))
      change 1 + 1 + scanCode.ticks ((Local.pop 7).eval ((scanCounted (O := O)).eval^[i] s)) ≤ 8
      omega)
  simpa [scanRoutine, Routine.iterate, scanCounted, Nat.mul_comm] using bounded

end ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader
