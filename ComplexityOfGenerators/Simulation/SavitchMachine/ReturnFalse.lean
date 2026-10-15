import ComplexityOfGenerators.Simulation.SavitchMachine.FieldCounter

/-! The unsuccessful-return branch of Savitch's recursion, implemented by
finite-control instructions and a bounded in-place midpoint counter. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

theorem memory_set_midpoint (f : Sav.Frm) (fs : List Sav.Frm) (m : List Bool) :
    Function.update (memory (f :: fs) (fun _ => [])) (src 5)
      (m.map some ++ none :: column fs 5) = memory ({f with m := m} :: fs) (fun _ => []) := by
  funext i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · change Function.update (memory (f :: fs) (fun _ => [])) (src 5)
      (m.map some ++ none :: column fs 5) (src j) = memory ({f with m := m} :: fs) (fun _ => []) (src j)
    simp only [Function.update_apply, src_inj, memory_src]
    fin_cases j <;> simp [column_cons, field]
  · change Function.update (memory (f :: fs) (fun _ => [])) (src 5)
      (m.map some ++ none :: column fs 5) (dst j) = memory ({f with m := m} :: fs) (fun _ => []) (dst j)
    simp only [Function.update_of_ne (src_ne_dst 5 j).symm, memory_dst]

theorem midpoint_column_length (f : Sav.Frm) (fs : List Sav.Frm) (m : List Bool)
    (length : m.length = f.m.length) (j : Fin 6) :
    (column ({f with m := m} :: fs) j).length = (column (f :: fs) j).length := by
  fin_cases j <;> simp [column_cons, field, length]

def returnFalseStart {Q : Type} (scan : Q) : Stmt Symbol Q Local 11 :=
  .load (fun v => ({v.1 with returned := some true}, none)) (.goto fun _ => scan)

def returnFalseFinish {Q : Type} (pop resume : Q) : Stmt Symbol Q Local 11 :=
  .branch (fun v => v.1.returned.getD false)
    (.load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => pop))
    (.pop (src 1) (fun v _ => v)
      (.push (src 1) (fun _ => some false)
        (.load (fun v => ({v.1 with returned := none}, none)) (.goto fun _ => resume))))

variable {Q : Type} (P : Q → Stmt Symbol Q Local 11)

theorem return_false_increment (entry scan restore finish : Q)
    (startTable : P entry = returnFalseStart scan)
    (scanTable : P scan = fieldCounterCode (src 5) (dst 5) scan restore)
    (restoreTable : P restore = transferCode (dst 5) (src 5) restore finish (fun _ => true))
    (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace P r (encoded entry ⟨false, a, some false, f :: fs⟩)
      (encoded finish ⟨false, a, some (bumpOver f.m), {f with m := bumpBits f.m} :: fs⟩) := by
  have count := fieldCounter_trace P (src 5) (dst 5) (src_ne_dst 5 5) scan restore finish
    scanTable restoreTable a true (memory (f :: fs) (fun _ => [])) f.m (column fs 5)
    (by simp [memory_src, column_cons, field]) (by simp) r (memory_bound _ r bound)
  rw [memory_set_midpoint] at count
  have next : TM2.step P (encoded entry ⟨false, a, some false, f :: fs⟩) =
      some (encoded scan ⟨false, a, some true, f :: fs⟩) := by
    simp [TM2.step, encoded, localConfig, startTable, returnFalseStart, TM2.stepAux, status]
  exact .step (memory_bound _ r bound) next count

theorem return_false_retry (finish pop resume : Q)
    (table : P finish = returnFalseFinish pop resume)
    (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) :
    TM2.step P (encoded finish ⟨false, a, some false, f :: fs⟩) =
      some (encoded resume ⟨false, a, none, {f with ph := false} :: fs⟩) := by
  simp only [TM2.step, encoded, localConfig, table, returnFalseFinish, TM2.stepAux, status,
    Option.getD_some, memory_src, column_cons]
  simp only [field, Matrix.cons_val_one, Matrix.cons_val_zero, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.tail_cons, Function.update_self, Function.update_idem]
  have tape := memory_set_phase f fs false
  simp only [memory_src, column_cons, field, Matrix.cons_val_one, Matrix.cons_val_zero,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.tail_cons] at tape
  rw [tape]
  rfl

theorem return_false_overflow (finish pop resume : Q)
    (table : P finish = returnFalseFinish pop resume)
    (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) :
    TM2.step P (encoded finish ⟨false, a, some true, f :: fs⟩) =
      some (encoded pop ⟨false, a, some false, f :: fs⟩) := by
  simp [TM2.step, encoded, localConfig, table, returnFalseFinish, TM2.stepAux, status]

/-- A failed recursive call either tries the next midpoint, resetting the
phase, or propagates failure after exhausting all midpoints. -/
theorem return_false_trace (entry scan restore finish resume : Q) (loadPhase erasePhase : ℕ → Q)
    (startTable : P entry = returnFalseStart scan)
    (scanTable : P scan = fieldCounterCode (src 5) (dst 5) scan restore)
    (restoreTable : P restore = transferCode (dst 5) (src 5) restore finish (fun _ => true))
    (finishTable : P finish = returnFalseFinish (loadPhase 0) resume)
    (loadTable : ∀ j : Fin 6, P (loadPhase j.val) =
      transferCode (src j) (dst j) (loadPhase j.val) (loadPhase (j.val + 1)) Option.isSome)
    (eraseTable : ∀ j : Fin 6, P (erasePhase j.val) =
      clearCode (dst j) (erasePhase j.val) (erasePhase (j.val + 1)) (fun _ => true))
    (handoff : loadPhase 6 = erasePhase 0) (returned : erasePhase 6 = resume)
    (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace P r (encoded entry ⟨false, a, some false, f :: fs⟩)
      (encoded resume (Sav.step br ba z ⟨false, a, some false, f :: fs⟩)) := by
  have count := return_false_increment P entry scan restore finish startTable scanTable restoreTable a f fs r bound
  let bumped := {f with m := bumpBits f.m}
  have bumpedBound : ∀ j, (column (bumped :: fs) j).length ≤ r := by
    intro j
    rw [midpoint_column_length f fs _ (bumpBits_length f.m)]
    exact bound j
  cases overflow : bumpOver f.m with
  | false =>
      rw [overflow] at count
      have next := return_false_retry P finish (loadPhase 0) resume finishTable a bumped fs
      have finalBound : Within r (encoded resume ⟨false, a, none, {bumped with ph := false} :: fs⟩) :=
        memory_bound _ r (fun j => by rw [phase_column_length]; exact bumpedBound j)
      have path := count.trans (.step (memory_bound _ r bumpedBound) next (.refl _ finalBound))
      simpa only [Sav.step_ret_false_bump br ba z a f fs overflow] using path
  | true =>
      rw [overflow] at count
      have next := return_false_overflow P finish (loadPhase 0) resume finishTable a bumped fs
      have tail := pop_frame P erasePhase loadPhase loadTable eraseTable handoff
        (status ⟨false, a, some false, bumped :: fs⟩) bumped fs r bumpedBound
      rw [returned] at tail
      have path := count.trans (.step (memory_bound _ r bumpedBound) next tail)
      simpa only [Sav.step_ret_false_over br ba z a f fs overflow, encoded, status] using path

end ComplexityOfGenerators.Simulation.SavitchMachine
