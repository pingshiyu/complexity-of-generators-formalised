import ComplexityOfGenerators.Simulation.StackSpace.ReadFixed
import ComplexityOfGenerators.Simulation.SavitchMachine.BoundedDecode

/-! The work-window part of a configuration edge test. Both windows are read
cell by cell using a fixed finite-control symbol decoder. Only the source head
cell may change; its old symbol must match the transition-table observation.
All four stacks shrink throughout this routine. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindow

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

variable (symbols : ℕ)
abbrev Cell := Option (Fin symbols)

inductive Label
  | loop (seen : Bool)
  | left (seen atHead : Bool)
  | right (seen atHead : Bool) (old : Cell symbols)
  | finish (seen : Bool)
  | reject | done
  deriving DecidableEq, Fintype

/-- Native instructions can write a nonblank symbol or leave the cell alone. -/
def written (write : Option (Fin symbols)) (old : Cell symbols) : Cell symbols :=
  match write with | none => old | some symbol => some symbol

def leftNext (observed : Cell symbols) (seen atHead : Bool) : Option (Cell symbols) → Label symbols
  | none => .reject
  | some old => if atHead && decide (old ≠ observed) then .reject else .right seen atHead old

def rightNext (write : Option (Fin symbols)) (seen atHead : Bool) (old : Cell symbols) :
    Option (Cell symbols) → Label symbols
  | none => .reject
  | some new => if new = (if atHead then written symbols write old else old) then .loop seen else .reject

def program (observed : Cell symbols) (write : Option (Fin symbols)) :
    Label symbols → Stmt Symbol (Label symbols) Local 3
  | .loop seen => .peek 2 (fun v s => (v.1, s))
      (.branch (fun v => v.2.isSome)
        (.pop 2 (fun v _ => v) (.peek 3 (fun v s => (v.1, s))
          (.branch (fun v => v.2.isSome)
            (.pop 3 (fun v _ => v) (.load (fun v => (v.1, none)) (.goto fun _ => .left seen false)))
            (.load (fun v => (v.1, none)) (.goto fun _ => .left true (!seen))))))
        (.load (fun v => (v.1, none)) (.goto fun _ => .finish seen)))
  | .left seen atHead => readCodecCode 0 (FixedWidthCodec.optionFin symbols)
      (leftNext symbols observed seen atHead)
  | .right seen atHead old => readCodecCode 1 (FixedWidthCodec.optionFin symbols)
      (rightNext symbols write seen atHead old)
  | .finish seen => .peek 0 (fun v s => ({v.1 with returned := some (seen && s.isNone)}, none))
      (.peek 1 (fun v s => ({v.1 with returned := some (v.1.returned.getD false && s.isNone)}, none))
        (.peek 3 (fun v s => ({v.1 with returned := some (v.1.returned.getD false && s.isNone)}, none))
          (.goto fun _ => .done)))
  | .reject => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)
  | .done => .halt

/-- A fieldwise specification of the same test, also defined on malformed
windows. `seen` records whether the unique head cell has already been visited. -/
def test (observed : Cell symbols) (write : Option (Fin symbols)) :
    ℕ → ℕ → Bool → List Bool → List Bool → Bool
  | 0, head, seen, u, v => seen && decide (u = [] ∧ v = [] ∧ head = 0)
  | n + 1, head, seen, u, v =>
      let atHead := !seen && decide (head = 0)
      match (FixedWidthCodec.optionFin symbols).decode (u.take (symbols + 1)),
          (FixedWidthCodec.optionFin symbols).decode (v.take (symbols + 1)) with
      | some old, some new =>
          (!(atHead && decide (old ≠ observed))) &&
          decide (new = if atHead then written symbols write old else old) &&
          test observed write n (head - 1) (seen || decide (head = 0))
            (u.drop (symbols + 1)) (v.drop (symbols + 1))
      | _, _ => false

def registers (u v : List Bool) (count head : ℕ) : Fin 4 → List Symbol :=
  ![u.map some, v.map some, unary count, unary head]

private theorem registers_bound (u v : List Bool) (count head r : ℕ)
    (hu : u.length ≤ r) (hv : v.length ≤ r) (hc : count ≤ r) (hh : head ≤ r) :
    ∀ j, (registers u v count head j).length ≤ r := by
  intro j
  fin_cases j <;> simp [registers] <;> assumption

private theorem reject_trace (observed : Cell symbols) (write : Option (Fin symbols))
    (answer : Bool) (stk : Fin 4 → List Symbol) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace (program symbols observed write) r
      (localConfig .reject (carrying answer false) stk)
      (localConfig .done (carrying answer false) stk) := by
  exact .step bound (by simp [TM2.step, TM2.stepAux, localConfig, program, carrying]) (.refl _ bound)

/-- The complete work-window comparison is implemented by a finite stack
program, uniformly in the window length and head position. -/
theorem run (observed : Cell symbols) (write : Option (Fin symbols))
    (answer : Bool) (count head : ℕ) (seen : Bool) (u v : List Bool) (r : ℕ)
    (hu : u.length ≤ r) (hv : v.length ≤ r) (hc : count ≤ r) (hh : head ≤ r) :
    ∃ stk, Trace (program symbols observed write) r
      (localConfig (.loop seen) (carrying answer false) (registers u v count head))
      (localConfig .done (carrying answer (test symbols observed write count head seen u v)) stk) := by
  let P := program symbols observed write
  have initial := registers_bound u v count head r hu hv hc hh
  induction count generalizing head seen u v with
  | zero =>
      have first : TM2.step P (localConfig (.loop seen) (carrying answer false) (registers u v 0 head)) =
          some (localConfig (.finish seen) (carrying answer false) (registers u v 0 head)) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, registers]
      refine ⟨registers u v 0 head, .step initial first (.step initial ?_ (.refl _ initial))⟩
      cases u <;> cases v <;> cases head <;> cases seen <;>
        simp [P, program, TM2.step, TM2.stepAux, localConfig, registers, test, carrying, List.replicate_succ]
  | succ count ih =>
      let nextSeen := seen || decide (head = 0)
      let atHead := !seen && decide (head = 0)
      let ready := registers u v count (head - 1)
      have readyBound := registers_bound u v count (head - 1) r hu hv (by omega) (by omega)
      have first : TM2.step P (localConfig (.loop seen) (carrying answer false) (registers u v (count + 1) head)) =
          some (localConfig (.left nextSeen atHead) (carrying answer false) ready) := by
        cases head <;> cases seen <;>
          simp [P, program, TM2.step, TM2.stepAux, localConfig, registers, nextSeen, atHead, ready,
            List.replicate_succ, Function.update_apply]
        all_goals funext j; fin_cases j <;> simp [Function.update_apply]
      have leftRead := readCodec_trace P 0 (.left nextSeen atHead) (FixedWidthCodec.optionFin symbols)
        (FixedWidthCodec.exact_optionFin symbols) (leftNext symbols observed nextSeen atHead) rfl
        u (carrying answer false) ready rfl r readyBound
      let leftMemory := Function.update ready (0 : Fin 4) ((u.drop (symbols + 1)).map some)
      change Trace P r (localConfig (.left nextSeen atHead) (carrying answer false) ready)
        (localConfig (leftNext symbols observed nextSeen atHead
          ((FixedWidthCodec.optionFin symbols).decode (u.take (symbols + 1))))
          (carrying answer false) leftMemory) at leftRead
      have start := Trace.step (show Within r (localConfig (.loop seen) (carrying answer false)
        (registers u v (count + 1) head)) from initial) first leftRead
      cases leftValue : (FixedWidthCodec.optionFin symbols).decode (u.take (symbols + 1)) with
      | none =>
          simp only [leftValue, leftNext] at start
          refine ⟨leftMemory, ?_⟩
          simpa only [test, leftValue] using start.trans
            (reject_trace symbols observed write answer leftMemory r start.end_bound)
      | some old =>
          by_cases mismatch : (atHead && decide (old ≠ observed)) = true
          · simp only [leftValue, leftNext, mismatch, ↓reduceIte] at start
            refine ⟨leftMemory, ?_⟩
            have no : test symbols observed write (count + 1) head seen u v = false := by
              simp only [test, leftValue]
              cases (FixedWidthCodec.optionFin symbols).decode (v.take (symbols + 1)) with
              | none => rfl
              | some new =>
                  change ((!(atHead && decide (old ≠ observed))) && _ && _) = false
                  simp only [mismatch, Bool.not_true, Bool.false_and]
            rw [no]
            exact start.trans (reject_trace symbols observed write answer leftMemory r start.end_bound)
          · have agrees : (atHead && decide (old ≠ observed)) = false := Bool.eq_false_iff.mpr mismatch
            simp only [leftValue, leftNext, agrees, Bool.false_eq_true, ↓reduceIte] at start
            have rightRead := readCodec_trace P 1 (.right nextSeen atHead old) (FixedWidthCodec.optionFin symbols)
              (FixedWidthCodec.exact_optionFin symbols) (rightNext symbols write nextSeen atHead old) rfl
              v (carrying answer false) leftMemory (by simp [leftMemory, ready, registers]) r start.end_bound
            let rightMemory := Function.update leftMemory (1 : Fin 4) ((v.drop (symbols + 1)).map some)
            change Trace P r (localConfig (.right nextSeen atHead old) (carrying answer false) leftMemory)
              (localConfig (rightNext symbols write nextSeen atHead old
                ((FixedWidthCodec.optionFin symbols).decode (v.take (symbols + 1))))
                (carrying answer false) rightMemory) at rightRead
            have both := start.trans rightRead
            cases rightValue : (FixedWidthCodec.optionFin symbols).decode (v.take (symbols + 1)) with
            | none =>
                simp only [rightValue, rightNext] at both
                refine ⟨rightMemory, ?_⟩
                simpa only [test, leftValue, rightValue] using both.trans
                  (reject_trace symbols observed write answer rightMemory r both.end_bound)
            | some new =>
                by_cases updated : new = if atHead then written symbols write old else old
                · simp only [rightValue, rightNext, updated, ↓reduceIte] at both
                  have layout : rightMemory = registers (u.drop (symbols + 1)) (v.drop (symbols + 1)) count (head - 1) := by
                    funext j
                    fin_cases j <;> simp [rightMemory, leftMemory, ready, registers]
                  rw [layout] at both
                  obtain ⟨stk, tail⟩ := ih (head - 1) nextSeen (u.drop (symbols + 1)) (v.drop (symbols + 1))
                    (by simp; omega) (by simp; omega) (by omega) (by omega) both.end_bound
                  refine ⟨stk, ?_⟩
                  have yes : test symbols observed write (count + 1) head seen u v =
                      test symbols observed write count (head - 1) nextSeen (u.drop (symbols + 1)) (v.drop (symbols + 1)) := by
                    simp only [test, leftValue, rightValue]
                    change ((!(atHead && decide (old ≠ observed))) && decide (new = if atHead then written symbols write old else old) && _) = _
                    simp only [agrees, updated, decide_true, Bool.not_false, Bool.true_and, nextSeen]
                  rw [yes]
                  exact both.trans tail
                · simp only [rightValue, rightNext, updated, ↓reduceIte] at both
                  refine ⟨rightMemory, ?_⟩
                  have no : test symbols observed write (count + 1) head seen u v = false := by
                    simp only [test, leftValue, rightValue]
                    change ((!(atHead && decide (old ≠ observed))) && decide (new = if atHead then written symbols write old else old) && _) = false
                    simp [updated]
                  rw [no]
                  exact both.trans (reject_trace symbols observed write answer rightMemory r both.end_bound)

end ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindow
