import ComplexityOfGenerators.Simulation.SavitchMachine.Frames

/-! Store the six loaded fields as a frame, consuming temporary storage.
Fields are stored in reverse index order so the same representation invariant
describes both loading and storing. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Frames

open Turing StackSpace Complexity
set_option backward.isDefEq.respectTransparency false

def marked (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) : Memory :=
  Function.update (loading f fs (j.val + 1)) (src j) (none :: column fs j)

@[simp] theorem marked_src (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    marked f fs j (src j) = none :: column fs j := by simp [marked]

@[simp] theorem marked_dst (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    marked f fs j (dst j) = (field f j).reverse.map some := by
  simp [marked, (src_ne_dst j j).symm]

theorem marked_bound (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) (r : ℕ)
    (bound : ∀ i, (column (f :: fs) i).length ≤ r) : ∀ i, (marked f fs j i).length ≤ r := by
  intro i
  by_cases h : i = src j
  · subst i
    have b := bound j
    simp only [column_cons, List.length_append, List.length_map, List.length_cons] at b
    simp only [marked_src, List.length_cons]; omega
  · simpa [marked, h] using loading_bound f fs (j.val + 1) r bound i

theorem storing_previous (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    replaceTwo (marked f fs j) (dst j) (src j) [] (column (f :: fs) j) = loading f fs j.val := by
  funext i
  refine Fin.addCases (m := 6) (n := 6) (fun a => ?_) (fun a => ?_) i
  · change replaceTwo _ _ _ _ _ (src a) = loading f fs j.val (src a)
    simp only [replaceTwo, marked, Function.update_apply, (src_ne_dst a j), ↓reduceIte,
      loading_src]
    by_cases h : a = j
    · subst a; simp
    · have ne : a.val ≠ j.val := fun eq => h (Fin.ext eq)
      have hiff : a.val < j.val + 1 ↔ a.val < j.val := by omega
      simp [h, hiff]
  · change replaceTwo _ _ _ _ _ (dst a) = loading f fs j.val (dst a)
    have ne := (src_ne_dst j a).symm
    simp only [replaceTwo, marked, Function.update_apply, ne, ↓reduceIte, loading_dst]
    by_cases h : a = j
    · subst a; simp
    · have ne : a.val ≠ j.val := fun eq => h (Fin.ext eq)
      have hiff : a.val < j.val + 1 ↔ a.val < j.val := by omega
      simp [h, hiff]

variable {Q V : Type} (P : Q → Stmt Symbol Q (V × Option Symbol) 11)
variable (phase : ℕ → Q) (loop : Fin 6 → Q)
variable (markTable : ∀ j : Fin 6,
  P (phase (j.val + 1)) = .push (src j) (fun _ => none) (.goto fun _ => loop j))
variable (copyTable : ∀ j : Fin 6,
  P (loop j) = transferCode (dst j) (src j) (loop j) (phase j.val) (fun _ => true))

include markTable copyTable

theorem store_field (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) (r : ℕ)
    (bound : ∀ i, (column (f :: fs) i).length ≤ r) :
    Trace P r (localConfig (phase (j.val + 1)) v (loading f fs (j.val + 1)))
      (localConfig (phase j.val) v (loading f fs j.val)) := by
  have first : TM2.step P (localConfig (phase (j.val + 1)) v (loading f fs (j.val + 1))) =
      some (localConfig (loop j) v (marked f fs j)) := by
    simp [TM2.step, localConfig, markTable, TM2.stepAux, marked]
  have tail := transfer_all P (dst j) (src j) (src_ne_dst j j).symm (loop j) (phase j.val)
    (fun _ => true) (copyTable j) v (marked f fs j) (by simp) r (marked_bound f fs j r bound) (by
      have b := bound j
      simpa [Nat.add_assoc] using b)
  have finish : replaceTwo (marked f fs j) (dst j) (src j) []
      ((marked f fs j (dst j)).reverse ++ marked f fs j (src j)) = loading f fs j.val := by
    simpa only [marked_dst, marked_src, ← List.map_reverse, List.reverse_reverse, ← column_cons] using
      storing_previous f fs j
  rw [finish] at tail
  exact .step (loading_bound f fs (j.val + 1) r bound) first tail

/-- Pushing a frame consumes all temporary field stacks and leaves the
suspended frame columns intact. The statement uses the actual library frame. -/
theorem store_frame (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace P r (localConfig (phase 6) v (memory fs (fun j => (field f j).reverse)))
      (localConfig (phase 0) v (memory (f :: fs) (fun _ => []))) := by
  have walk (p : ℕ) (hp : p ≤ 6) :
      Trace P r (localConfig (phase p) v (loading f fs p)) (localConfig (phase 0) v (loading f fs 0)) := by
    induction p with
    | zero => exact .refl _ (loading_bound f fs 0 r bound)
    | succ p ih =>
        exact (store_field P phase loop markTable copyTable v f fs ⟨p, by omega⟩ r bound).trans (ih (by omega))
  simpa only [loading_zero, loading_six] using walk 6 (by omega)

end ComplexityOfGenerators.Simulation.SavitchMachine.Frames
