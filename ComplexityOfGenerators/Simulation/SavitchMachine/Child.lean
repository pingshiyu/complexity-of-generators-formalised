import ComplexityOfGenerators.Simulation.SavitchMachine.ChildFields
import ComplexityOfGenerators.Simulation.SavitchMachine.ReturnTrue

/-! Pushing a complete recursive child onto the six frame columns. Fields
are installed from left to right; every field that a later recipe reads still
belongs to the parent. No suspended frame is overwritten. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Frames

open Turing StackSpace Complexity
set_option backward.isDefEq.respectTransparency false

def pushing (child : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) : Memory :=
  Fin.addCases (m := 6) (n := 6) (motive := fun _ => List Symbol)
    (fun j => if j.val < p then column (child :: fs) j else column fs j)
    (fun _ => [])

@[simp] theorem pushing_src (child : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) (j : Fin 6) :
    pushing child fs p (src j) = if j.val < p then column (child :: fs) j else column fs j := by
  simp only [pushing, src, Fin.addCases_left]

@[simp] theorem pushing_dst (child : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) (j : Fin 6) :
    pushing child fs p (dst j) = [] := by simp only [pushing, dst, Fin.addCases_right]

@[simp] theorem pushing_zero (child : Sav.Frm) (fs : List Sav.Frm) :
    pushing child fs 0 = memory fs (fun _ => []) := by simp [pushing, memory]

@[simp] theorem pushing_six (child : Sav.Frm) (fs : List Sav.Frm) :
    pushing child fs 6 = memory (child :: fs) (fun _ => []) := by simp [pushing, memory]

theorem pushing_bound (child : Sav.Frm) (fs : List Sav.Frm) (p r : ℕ)
    (bound : ∀ j, (column (child :: fs) j).length ≤ r) :
    ∀ j, (pushing child fs p j).length ≤ r := by
  intro i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · change (pushing child fs p (src j)).length ≤ r
    rw [pushing_src]
    split
    · exact bound j
    · have h := bound j
      simp only [column_cons, List.length_append, List.length_map, List.length_cons] at h
      omega
  · change (pushing child fs p (dst j)).length ≤ r
    simp

theorem pushing_next (child : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    Function.update (pushing child fs j.val) (src j) (column (child :: fs) j) =
      pushing child fs (j.val + 1) := by
  funext i
  refine Fin.addCases (m := 6) (n := 6) (fun a => ?_) (fun a => ?_) i
  · change Function.update (pushing child fs j.val) (src j) (column (child :: fs) j) (src a) =
      pushing child fs (j.val + 1) (src a)
    simp only [Function.update_apply, src_inj, pushing_src]
    by_cases h : a = j
    · subst a; simp
    · have ne : a.val ≠ j.val := fun eq => h (Fin.ext eq)
      have hiff : a.val < j.val + 1 ↔ a.val < j.val := by omega
      simp [h, hiff]
  · change Function.update (pushing child fs j.val) (src j) (column (child :: fs) j) (dst a) =
      pushing child fs (j.val + 1) (dst a)
    simp only [Function.update_of_ne (src_ne_dst j a).symm, pushing_dst]

end ComplexityOfGenerators.Simulation.SavitchMachine.Frames

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

variable {Q V : Type} (P : Q → Stmt Symbol Q (V × Option Symbol) 11)
variable (phase : ℕ → Q) (label : ℕ → Fin 9 → Q)
variable (f : Sav.Frm) (fs : List Sav.Frm)
variable (entry : ∀ j : Fin 6, phase j.val = label j.val 0)
variable (table : ∀ (j : Fin 6) pc, P (label j.val pc) =
  fieldCode j (childRecipe f.kind f.ph j) (label j.val) (phase (j.val + 1)) pc)
include entry table

theorem child_field_trace (v : V) (j : Fin 6) (r : ℕ)
    (bound : ∀ i, (column (Sav.child (List.replicate f.m.length false) f :: f :: fs) i).length ≤ r) :
    Trace P r
      (localConfig (phase j.val) v (pushing (Sav.child (List.replicate f.m.length false) f) (f :: fs) j.val))
      (localConfig (phase (j.val + 1)) v
        (pushing (Sav.child (List.replicate f.m.length false) f) (f :: fs) (j.val + 1))) := by
  let child := Sav.child (List.replicate f.m.length false) f
  have path := field_trace P j (childRecipe f.kind f.ph j) (label j.val) (phase (j.val + 1))
    (table j) v (pushing child (f :: fs) j.val) f (by
      intro source reads
      have le := childRecipe_source f.kind f.ph j source reads
      refine ⟨column fs source, ?_⟩
      simp only [pushing_src, show ¬source.val < j.val by omega, ↓reduceIte, column_cons])
    (by simp) (by simp) r (pushing_bound child (f :: fs) j.val r bound) (by
      simpa only [childRecipe_value, pushing_src, lt_self_iff_false, ↓reduceIte,
        column_cons, List.length_append, List.length_map, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound j)
  rw [← entry j, childRecipe_value] at path
  have finish : Function.update (pushing child (f :: fs) j.val) (src j)
      ((field child j).map some ++ none :: pushing child (f :: fs) j.val (src j)) =
      pushing child (f :: fs) (j.val + 1) := by
    simpa only [pushing_src, lt_self_iff_false, ↓reduceIte, ← column_cons] using pushing_next child (f :: fs) j
  rw [finish] at path
  exact path

/-- The six finite field routines implement the library's complete child
constructor, leaving all parent frames and scratch registers intact. -/
theorem child_frame_trace (v : V) (r : ℕ)
    (bound : ∀ j, (column (Sav.child (List.replicate f.m.length false) f :: f :: fs) j).length ≤ r) :
    Trace P r (localConfig (phase 0) v (memory (f :: fs) (fun _ => [])))
      (localConfig (phase 6) v
        (memory (Sav.child (List.replicate f.m.length false) f :: f :: fs) (fun _ => []))) := by
  let child := Sav.child (List.replicate f.m.length false) f
  have walk (p : ℕ) (hp : p ≤ 6) : Trace P r
      (localConfig (phase 0) v (pushing child (f :: fs) 0))
      (localConfig (phase p) v (pushing child (f :: fs) p)) := by
    induction p with
    | zero => exact .refl _ (pushing_bound child (f :: fs) 0 r bound)
    | succ p ih =>
        exact (ih (by omega)).trans
          (child_field_trace P phase label f fs entry table v ⟨p, by omega⟩ r bound)
  simpa only [pushing_zero, pushing_six] using walk 6 (by omega)

omit entry table in
/-- Recursive descent is the actual `Sav.step`, with the fixed-width zero
midpoint supplied by the configuration encoding. -/
theorem child_trace (P : Q → Stmt Symbol Q Local 11)
    (entry : ∀ j : Fin 6, phase j.val = label j.val 0)
    (table : ∀ (j : Fin 6) pc, P (label j.val pc) =
      fieldCode j (childRecipe f.kind f.ph j) (label j.val) (phase (j.val + 1)) pc)
    (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (zero : z = List.replicate f.m.length false) (a : Bool) (nonbase : f.lvl ≠ []) (r : ℕ)
    (bound : ∀ j, (column (Sav.child z f :: f :: fs) j).length ≤ r) :
    Trace P r (encoded (phase 0) ⟨false, a, none, f :: fs⟩)
      (encoded (phase 6) (Sav.step br ba z ⟨false, a, none, f :: fs⟩)) := by
  subst z
  rw [Sav.step_push br ba _ a f fs nonbase]
  exact child_frame_trace P phase label f fs entry table (status ⟨false, a, none, f :: fs⟩) r bound

end ComplexityOfGenerators.Simulation.SavitchMachine
