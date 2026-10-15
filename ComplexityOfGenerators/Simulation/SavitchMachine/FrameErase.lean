import ComplexityOfGenerators.Simulation.SavitchMachine.FrameSpace
import ComplexityOfGenerators.Simulation.StackSpace.Clear

/-! Returning from a Savitch call: discard the loaded frame's temporary
fields and expose the unchanged parent frames. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Frames

open Turing StackSpace Complexity
set_option backward.isDefEq.respectTransparency false

def erasing (f : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) : Memory :=
  Fin.addCases (m := 6) (n := 6) (motive := fun _ => List Symbol)
    (fun j => column fs j)
    (fun j => if j.val < p then [] else (field f j).reverse.map some)

@[simp] theorem erasing_src (f : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) (j : Fin 6) :
    erasing f fs p (src j) = column fs j := by
  simp only [erasing, src, Fin.addCases_left]

@[simp] theorem erasing_dst (f : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) (j : Fin 6) :
    erasing f fs p (dst j) = if j.val < p then [] else (field f j).reverse.map some := by
  simp only [erasing, dst, Fin.addCases_right]

@[simp] theorem erasing_zero (f : Sav.Frm) (fs : List Sav.Frm) :
    erasing f fs 0 = memory fs (fun j => (field f j).reverse) := by simp [erasing, memory]

@[simp] theorem erasing_six (f : Sav.Frm) (fs : List Sav.Frm) :
    erasing f fs 6 = memory fs (fun _ => []) := by simp [erasing, memory]

theorem erasing_bound (f : Sav.Frm) (fs : List Sav.Frm) (p r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) : ∀ j, (erasing f fs p j).length ≤ r := by
  intro i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · change (erasing f fs p (src j)).length ≤ r
    rw [erasing_src]
    have h := bound j
    simp only [column_cons, List.length_append, List.length_map, List.length_cons] at h
    omega
  · change (erasing f fs p (dst j)).length ≤ r
    rw [erasing_dst]
    split
    · simp
    · have h := bound j
      simp only [column_cons, List.length_append, List.length_map, List.length_cons] at h
      simp only [List.length_map, List.length_reverse]; omega

theorem erasing_next (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    Function.update (erasing f fs j.val) (dst j) [] = erasing f fs (j.val + 1) := by
  funext i
  refine Fin.addCases (m := 6) (n := 6) (fun a => ?_) (fun a => ?_) i
  · change Function.update (erasing f fs j.val) (dst j) ([] : List Symbol) (src a) = erasing f fs (j.val + 1) (src a)
    simp only [Function.update_of_ne (src_ne_dst a j), erasing_src]
  · change Function.update (erasing f fs j.val) (dst j) ([] : List Symbol) (dst a) = erasing f fs (j.val + 1) (dst a)
    simp only [Function.update_apply, dst_inj, erasing_dst]
    by_cases h : a = j
    · subst a; simp
    · have ne : a.val ≠ j.val := fun eq => h (Fin.ext eq)
      have hiff : a.val < j.val + 1 ↔ a.val < j.val := by omega
      simp [h, hiff]

variable {Q V : Type} (P : Q → Stmt Symbol Q (V × Option Symbol) 11) (phase : ℕ → Q)
variable (table : ∀ j : Fin 6,
  P (phase j.val) = clearCode (dst j) (phase j.val) (phase (j.val + 1)) (fun _ => true))

include table

theorem erase_field (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) (r : ℕ)
    (bound : ∀ i, (column (f :: fs) i).length ≤ r) :
    Trace P r (localConfig (phase j.val) v (erasing f fs j.val))
      (localConfig (phase (j.val + 1)) v (erasing f fs (j.val + 1))) := by
  have path := clear_all P (dst j) (phase j.val) (phase (j.val + 1)) (fun _ => true) (table j)
    v (erasing f fs j.val) (by simp) r (erasing_bound f fs j.val r bound)
  rw [erasing_next f fs j] at path
  exact path

theorem erase_frame (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ i, (column (f :: fs) i).length ≤ r) :
    Trace P r (localConfig (phase 0) v (memory fs (fun j => (field f j).reverse)))
      (localConfig (phase 6) v (memory fs (fun _ => []))) := by
  have walk (p : ℕ) (hp : p ≤ 6) :
      Trace P r (localConfig (phase 0) v (erasing f fs 0)) (localConfig (phase p) v (erasing f fs p)) := by
    induction p with
    | zero => exact .refl _ (erasing_bound f fs 0 r bound)
    | succ p ih => exact (ih (by omega)).trans (erase_field P phase table v f fs ⟨p, by omega⟩ r bound)
  simpa only [erasing_zero, erasing_six] using walk 6 (by omega)

omit table in
/-- Loading and erasing implement popping exactly one complete library frame.
The suspended stack and the caller's finite local variables are preserved. -/
theorem pop_frame (loadPhase : ℕ → Q)
    (loadTable : ∀ j : Fin 6, P (loadPhase j.val) =
      transferCode (src j) (dst j) (loadPhase j.val) (loadPhase (j.val + 1)) Option.isSome)
    (eraseTable : ∀ j : Fin 6,
      P (phase j.val) = clearCode (dst j) (phase j.val) (phase (j.val + 1)) (fun _ => true))
    (handoff : loadPhase 6 = phase 0) (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ i, (column (f :: fs) i).length ≤ r) :
    Trace P r (localConfig (loadPhase 0) v (memory (f :: fs) (fun _ => [])))
      (localConfig (phase 6) v (memory fs (fun _ => []))) := by
  have first := load_frame P loadPhase loadTable v f fs r bound
  rw [handoff] at first
  exact first.trans (erase_frame P phase eraseTable v f fs r bound)

end ComplexityOfGenerators.Simulation.SavitchMachine.Frames
