import ComplexityOfGenerators.Simulation.SavitchMachine.Child
import ComplexityOfGenerators.Simulation.SavitchMachine.ReturnFalse

/-! The finite control table of the Savitch interpreter. Its recursive stack
operations are concrete. The configuration-graph base test is a separately
supplied subprogram, entered only at depth zero. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

inductive Label (B : Type)
  | dispatch | returnTrue | returnFalse | count | restoreCount | finishCount
  | load (field : Fin 6)
  | erase (field : Fin 6)
  | child (kind phase : Bool) (field : Fin 6) (pc : Fin 9)
  | base (pc : B)
  deriving DecidableEq, Fintype

variable {B : Type}

def erasePhase (p : ℕ) : Label B := if h : p < 6 then .erase ⟨p, h⟩ else .dispatch

def loadPhase (p : ℕ) : Label B := if h : p < 6 then .load ⟨p, h⟩ else erasePhase 0

def childPhase (kind phase : Bool) (p : ℕ) : Label B :=
  if h : p < 6 then .child kind phase ⟨p, h⟩ 0 else .dispatch

def jumpClean (target : Label B) : Stmt Symbol (Label B) Local 11 :=
  .load (fun v => (v.1, none)) (.goto fun _ => target)

def chooseChild (phase : Bool) : Stmt Symbol (Label B) Local 11 :=
  .peek (src 0) (fun v s => (v.1, s))
    (.branch (fun v => v.2.join.getD false)
      (jumpClean (childPhase true phase 0)) (jumpClean (childPhase false phase 0)))

def dispatchCode (baseEntry : B) : Stmt Symbol (Label B) Local 11 :=
  .branch (fun v => v.1.done) .halt
    (.peek (src 0) (fun v s => (v.1, s))
      (.branch (fun v => v.2.isSome)
        (.branch (fun v => v.1.returned.isSome)
          (.branch (fun v => v.1.returned.getD false)
            (jumpClean .returnTrue) (jumpClean .returnFalse))
          (.peek (src 2) (fun v s => (v.1, s))
            (.branch (fun v => v.2.join.isSome)
              (.peek (src 1) (fun v s => (v.1, s))
                (.branch (fun v => v.2.join.getD false) (chooseChild true) (chooseChild false)))
              (jumpClean (.base baseEntry)))))
        (.load (fun v => (⟨true, v.1.returned.getD false, v.1.returned⟩, none))
          (.goto fun _ => .dispatch))))

/-- Every non-base instruction is fixed by this table. Base routines use the
same stack alphabet and finite local variables and can return to `dispatch`. -/
def program (baseEntry : B) (base : B → Stmt Symbol (Label B) Local 11) :
    Label B → Stmt Symbol (Label B) Local 11
  | .dispatch => dispatchCode baseEntry
  | .returnTrue => returnTrueCode (loadPhase 0) .dispatch
  | .returnFalse => returnFalseStart .count
  | .count => fieldCounterCode (src 5) (dst 5) .count .restoreCount
  | .restoreCount => transferCode (dst 5) (src 5) .restoreCount .finishCount (fun _ => true)
  | .finishCount => returnFalseFinish (loadPhase 0) .dispatch
  | .load j => transferCode (src j) (dst j) (loadPhase j.val) (loadPhase (j.val + 1)) Option.isSome
  | .erase j => clearCode (dst j) (erasePhase j.val) (erasePhase (j.val + 1)) (fun _ => true)
  | .child kind phase j pc => fieldCode j (childRecipe kind phase j)
      (fun pc => .child kind phase j pc) (childPhase kind phase (j.val + 1)) pc
  | .base pc => base pc

variable (baseEntry : B) (base : B → Stmt Symbol (Label B) Local 11)

@[simp] theorem program_load (j : Fin 6) :
    program baseEntry base (loadPhase j.val) =
      transferCode (src j) (dst j) (loadPhase j.val) (loadPhase (j.val + 1)) Option.isSome := by
  simp only [loadPhase, j.isLt, ↓reduceDIte, program]

@[simp] theorem program_erase (j : Fin 6) :
    program baseEntry base (erasePhase j.val) =
      clearCode (dst j) (erasePhase j.val) (erasePhase (j.val + 1)) (fun _ => true) := by
  simp only [erasePhase, j.isLt, ↓reduceDIte, program]

theorem program_return_true (br : List Bool → List Bool → Bool)
    (ba : List Bool → Bool) (z : List Bool) (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm)
    (r : ℕ) (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace (program baseEntry base) r (encoded .returnTrue ⟨false, a, some true, f :: fs⟩)
      (encoded .dispatch (Sav.step br ba z ⟨false, a, some true, f :: fs⟩)) :=
  return_true_trace (program baseEntry base) .returnTrue .dispatch loadPhase erasePhase rfl
    (program_load baseEntry base) (program_erase baseEntry base) rfl rfl br ba z a f fs r bound

theorem program_return_false (br : List Bool → List Bool → Bool)
    (ba : List Bool → Bool) (z : List Bool) (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm)
    (r : ℕ) (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace (program baseEntry base) r (encoded .returnFalse ⟨false, a, some false, f :: fs⟩)
      (encoded .dispatch (Sav.step br ba z ⟨false, a, some false, f :: fs⟩)) :=
  return_false_trace (program baseEntry base) .returnFalse .count .restoreCount .finishCount
    .dispatch loadPhase erasePhase rfl rfl rfl rfl
    (program_load baseEntry base) (program_erase baseEntry base) rfl rfl br ba z a f fs r bound

theorem program_child (br : List Bool → List Bool → Bool) (ba : List Bool → Bool)
    (f : Sav.Frm) (fs : List Sav.Frm)
    (z : List Bool) (zero : z = List.replicate f.m.length false) (a : Bool)
    (nonbase : f.lvl ≠ []) (r : ℕ)
    (bound : ∀ j, (column (Sav.child z f :: f :: fs) j).length ≤ r) :
    Trace (program baseEntry base) r (encoded (childPhase f.kind f.ph 0) ⟨false, a, none, f :: fs⟩)
      (encoded .dispatch (Sav.step br ba z ⟨false, a, none, f :: fs⟩)) := by
  exact child_trace (childPhase f.kind f.ph)
    (fun p pc => .child f.kind f.ph ⟨p % 6, Nat.mod_lt _ (by decide)⟩ pc) f fs
    (program baseEntry base)
    (fun j => by simp [childPhase, j.isLt, Nat.mod_eq_of_lt j.isLt])
    (fun j pc => by simp only [Nat.mod_eq_of_lt j.isLt, program]) br ba z zero a nonbase r bound

theorem dispatch_empty (a : Bool) (returned : Option Bool) :
    TM2.step (program baseEntry base) (encoded .dispatch ⟨false, a, returned, []⟩) =
      some (encoded .dispatch ⟨true, returned.getD false, returned, []⟩) := by
  simp [TM2.step, program, dispatchCode, encoded, localConfig, status, TM2.stepAux,
    memory_src]

theorem dispatch_return (a result : Bool) (f : Sav.Frm) (fs : List Sav.Frm) :
    TM2.step (program baseEntry base) (encoded .dispatch ⟨false, a, some result, f :: fs⟩) =
      some (encoded (if result then .returnTrue else .returnFalse) ⟨false, a, some result, f :: fs⟩) := by
  cases result <;> simp [TM2.step, program, dispatchCode, encoded, localConfig, status, TM2.stepAux,
    memory_src, column_cons, field, jumpClean]

theorem dispatch_base (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (level : f.lvl = []) :
    TM2.step (program baseEntry base) (encoded .dispatch ⟨false, a, none, f :: fs⟩) =
      some (encoded (.base baseEntry) ⟨false, a, none, f :: fs⟩) := by
  simp [TM2.step, program, dispatchCode, encoded, localConfig, status, TM2.stepAux,
    memory_src, column_cons, field, jumpClean, level]

theorem dispatch_child (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (level : f.lvl ≠ []) :
    TM2.step (program baseEntry base) (encoded .dispatch ⟨false, a, none, f :: fs⟩) =
      some (encoded (childPhase f.kind f.ph 0) ⟨false, a, none, f :: fs⟩) := by
  obtain ⟨bit, rest, head⟩ := List.exists_cons_of_ne_nil level
  cases phase : f.ph <;> cases kind : f.kind <;>
    simp [TM2.step, program, dispatchCode, encoded, localConfig, status, TM2.stepAux,
      memory_src, column_cons, field, jumpClean, chooseChild, head, phase, kind]

end ComplexityOfGenerators.Simulation.SavitchMachine
