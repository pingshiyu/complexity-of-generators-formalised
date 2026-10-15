import ComplexityOfGenerators.Simulation.SavitchMachine.FrameErase

/-! Native stack-program implementation of the successful-return branch of
Complexitylib's Savitch interpreter. Parent frames and return status reside in
their actual tape and finite-control representations. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

@[ext] structure Status where
  done : Bool
  answer : Bool
  returned : Option Bool
  deriving DecidableEq, Fintype

def status (s : Sav.Sst) : Status := ⟨s.done, s.ans, s.ret⟩

abbrev Local := Status × Option Symbol

def encoded {Q : Type} (q : Q) (s : Sav.Sst) : Source Symbol Q Local 11 :=
  localConfig q (status s) (memory s.stk (fun _ => []))

theorem memory_bound (fs : List Sav.Frm) (r : ℕ) (bound : ∀ j, (column fs j).length ≤ r) :
    ∀ j, (memory fs (fun _ => []) j).length ≤ r := by
  intro i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · simpa only [memory, Fin.addCases_left] using bound j
  · simp only [memory, Fin.addCases_right, List.map_nil, List.length_nil, Nat.zero_le]

theorem memory_set_phase (f : Sav.Frm) (fs : List Sav.Frm) (phase : Bool) :
    Function.update (memory (f :: fs) (fun _ => [])) (src 1)
      (some phase :: (memory (f :: fs) (fun _ => []) (src 1)).tail) =
      memory ({f with ph := phase} :: fs) (fun _ => []) := by
  funext i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · change Function.update (memory (f :: fs) (fun _ => [])) (src 1)
      (some phase :: (memory (f :: fs) (fun _ => []) (src 1)).tail) (src j) =
      memory ({f with ph := phase} :: fs) (fun _ => []) (src j)
    simp only [Function.update_apply, src_inj, memory_src]
    fin_cases j <;> simp [field, column_cons]
  · change Function.update (memory (f :: fs) (fun _ => [])) (src 1)
      (some phase :: (memory (f :: fs) (fun _ => []) (src 1)).tail) (dst j) =
      memory ({f with ph := phase} :: fs) (fun _ => []) (dst j)
    simp only [Function.update_of_ne (src_ne_dst 1 j).symm, memory_dst]

theorem phase_column_length (f : Sav.Frm) (fs : List Sav.Frm) (phase : Bool) (j : Fin 6) :
    (column ({f with ph := phase} :: fs) j).length = (column (f :: fs) j).length := by
  fin_cases j <;> simp [column_cons, field]

def returnTrueCode {Q : Type} (pop resume : Q) : Stmt Symbol Q Local 11 :=
  .peek (src 1) (fun v s => (v.1, s))
    (.branch (fun v => decide (v.2 = some (some true)))
      (.load (fun v => (v.1, none)) (.goto fun _ => pop))
      (.pop (src 1) (fun v _ => v)
        (.push (src 1) (fun _ => some true)
          (.load (fun v => ({v.1 with returned := none}, none)) (.goto fun _ => resume)))))

variable {Q : Type} (P : Q → Stmt Symbol Q Local 11) (entry pop resume : Q)
variable (table : P entry = returnTrueCode pop resume)
include table

theorem return_true_first (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (first : f.ph = false) :
    TM2.step P (encoded entry ⟨false, a, some true, f :: fs⟩) =
      some (encoded resume ⟨false, a, none, {f with ph := true} :: fs⟩) := by
  simp only [TM2.step, encoded, localConfig, table, returnTrueCode, TM2.stepAux,
    memory_src, column_cons]
  simp only [field, Matrix.cons_val_one, Matrix.cons_val_zero, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.head?_cons, first]
  simp only [List.tail_cons, Function.update_self,
    Function.update_idem]
  have tape := memory_set_phase f fs true
  simp only [memory_src, column_cons, field, Matrix.cons_val_one, Matrix.cons_val_zero,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.tail_cons] at tape
  rw [tape]
  rfl

theorem return_true_second (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (second : f.ph = true) :
    TM2.step P (encoded entry ⟨false, a, some true, f :: fs⟩) =
      some (encoded pop ⟨false, a, some true, f :: fs⟩) := by
  simp [TM2.step, encoded, localConfig, table, returnTrueCode, TM2.stepAux, memory_src,
    column_cons, field, second]

omit table in
/-- One successful recursive call advances the phase; a second successful
call pops the frame. Both cases implement the actual library step. -/
theorem return_true_trace (loadPhase erasePhase : ℕ → Q)
    (entryTable : P entry = returnTrueCode (loadPhase 0) resume)
    (loadTable : ∀ j : Fin 6, P (loadPhase j.val) =
      transferCode (src j) (dst j) (loadPhase j.val) (loadPhase (j.val + 1)) Option.isSome)
    (eraseTable : ∀ j : Fin 6, P (erasePhase j.val) =
      clearCode (dst j) (erasePhase j.val) (erasePhase (j.val + 1)) (fun _ => true))
    (handoff : loadPhase 6 = erasePhase 0) (returned : erasePhase 6 = resume)
    (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace P r (encoded entry ⟨false, a, some true, f :: fs⟩)
      (encoded resume (Sav.step br ba z ⟨false, a, some true, f :: fs⟩)) := by
  cases phase : f.ph with
  | false =>
      have next := return_true_first P entry (loadPhase 0) resume entryTable a f fs phase
      have targetBound : Within r (encoded resume ⟨false, a, none, {f with ph := true} :: fs⟩) := by
        exact memory_bound _ r (fun j => by rw [phase_column_length]; exact bound j)
      have path := Trace.step (show Within r (encoded entry ⟨false, a, some true, f :: fs⟩) from
        memory_bound _ r bound) next (.refl _ targetBound)
      simpa only [Sav.step_ret_true_of_ph_false br ba z a f fs phase] using path
  | true =>
      have next := return_true_second P entry (loadPhase 0) resume entryTable a f fs phase
      have tail := pop_frame P erasePhase loadPhase loadTable eraseTable handoff
        (status ⟨false, a, some true, f :: fs⟩) f fs r bound
      rw [returned] at tail
      have path := Trace.step (show Within r (encoded entry ⟨false, a, some true, f :: fs⟩) from
        memory_bound _ r bound) next tail
      simpa only [Sav.step_ret_true_ph br ba z a f fs phase, encoded, status] using path

end ComplexityOfGenerators.Simulation.SavitchMachine
