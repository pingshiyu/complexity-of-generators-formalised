import ComplexityOfGenerators.Simulation.StackSpace.Transfer
import ComplexityOfGenerators.Foundations.SavitchStack

/-!
# Savitch frames on finite stacks

Six columns store the six fields of the library's `Sav.Frm`. A delimiter
separates successive frames in each column. Six temporary stacks hold a loaded
frame in reverse order. Reading a frame consumes only its fields, preserving
all suspended parent frames below them.
-/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Frames

open Turing StackSpace Complexity
set_option backward.isDefEq.respectTransparency false

abbrev Symbol := Option Bool
abbrev Memory := Fin 12 → List Symbol

def field (f : Sav.Frm) : Fin 6 → List Bool := ![[f.kind], [f.ph], f.lvl, f.u, f.v, f.m]

def column (fs : List Sav.Frm) (j : Fin 6) : List Symbol :=
  fs.flatMap fun f => (field f j).map some ++ [none]

@[simp] theorem column_nil (j : Fin 6) : column [] j = [] := rfl

@[simp] theorem column_cons (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    column (f :: fs) j = (field f j).map some ++ none :: column fs j := by
  simp [column, List.append_assoc]

def src (j : Fin 6) : Fin 12 := Fin.castAdd 6 j
def dst (j : Fin 6) : Fin 12 := Fin.natAdd 6 j

theorem src_ne_dst (i j : Fin 6) : src i ≠ dst j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [src, dst, Fin.val_castAdd, Fin.val_natAdd] at h'
  omega

@[simp] theorem src_inj {i j : Fin 6} : src i = src j ↔ i = j := by simpa only [src] using (Fin.castAdd_inj (n := 6) (a := i) (b := j))
@[simp] theorem dst_inj {i j : Fin 6} : dst i = dst j ↔ i = j := by simpa only [dst] using (Fin.natAdd_inj 6 (i := i) (j := j))

def memory (fs : List Sav.Frm) (registers : Fin 6 → List Bool) : Memory :=
  Fin.addCases (m := 6) (n := 6) (motive := fun _ => List Symbol) (fun j => column fs j) (fun j => (registers j).map some)

@[simp] theorem memory_src (fs : List Sav.Frm) (registers : Fin 6 → List Bool) (j : Fin 6) :
    memory fs registers (src j) = column fs j := by simp only [memory, src, Fin.addCases_left]

@[simp] theorem memory_dst (fs : List Sav.Frm) (registers : Fin 6 → List Bool) (j : Fin 6) :
    memory fs registers (dst j) = (registers j).map some := by simp only [memory, dst, Fin.addCases_right]

/-- After `p` fields have been read, precisely those columns have lost their
top field and the corresponding temporary stacks hold its reverse. -/
def loading (f : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) : Memory :=
  Fin.addCases (m := 6) (n := 6) (motive := fun _ => List Symbol)
    (fun j => if j.val < p then column fs j else column (f :: fs) j)
    (fun j => if j.val < p then (field f j).reverse.map some else [])

@[simp] theorem loading_src (f : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) (j : Fin 6) :
    loading f fs p (src j) = if j.val < p then column fs j else column (f :: fs) j := by
  simp only [loading, src, Fin.addCases_left]

@[simp] theorem loading_dst (f : Sav.Frm) (fs : List Sav.Frm) (p : ℕ) (j : Fin 6) :
    loading f fs p (dst j) = if j.val < p then (field f j).reverse.map some else [] := by
  simp only [loading, dst, Fin.addCases_right]

@[simp] theorem loading_zero (f : Sav.Frm) (fs : List Sav.Frm) :
    loading f fs 0 = memory (f :: fs) (fun _ => []) := by
  simp [loading, memory]

@[simp] theorem loading_six (f : Sav.Frm) (fs : List Sav.Frm) :
    loading f fs 6 = memory fs (fun j => (field f j).reverse) := by
  simp [loading, memory]

theorem loading_bound (f : Sav.Frm) (fs : List Sav.Frm) (p r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    ∀ j, (loading f fs p j).length ≤ r := by
  intro i
  refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
  · change (loading f fs p (src j)).length ≤ r
    rw [loading_src]
    split
    · have h := bound j; simp only [column_cons, List.length_append, List.length_cons, List.length_map] at h
      omega
    · exact bound j
  · change (loading f fs p (dst j)).length ≤ r
    rw [loading_dst]
    split
    · have h := bound j; simp only [column_cons, List.length_append, List.length_cons, List.length_map] at h
      simp only [List.length_map, List.length_reverse]; omega
    · simp

theorem loading_next (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) :
    replaceTwo (loading f fs j.val) (src j) (dst j) (column fs j) ((field f j).reverse.map some) =
      loading f fs (j.val + 1) := by
  funext i
  refine Fin.addCases (m := 6) (n := 6) (fun a => ?_) (fun a => ?_) i
  · change replaceTwo _ _ _ _ _ (src a) = loading f fs (j.val + 1) (src a)
    simp only [replaceTwo, Function.update_apply, (src_ne_dst a j), ↓reduceIte, loading_src]
    by_cases h : a = j
    · subst a; simp
    · have ne : a.val ≠ j.val := fun eq => h (Fin.ext eq)
      have hiff : a.val < j.val + 1 ↔ a.val < j.val := by omega
      simp [h, hiff]
  · change replaceTwo _ _ _ _ _ (dst a) = loading f fs (j.val + 1) (dst a)
    have ne := (src_ne_dst j a).symm
    simp only [replaceTwo, Function.update_apply, ne, ↓reduceIte, loading_dst]
    by_cases h : a = j
    · subst a; simp
    · have ne : a.val ≠ j.val := fun eq => h (Fin.ext eq)
      have hiff : a.val < j.val + 1 ↔ a.val < j.val := by omega
      simp [h, hiff]

variable {Q V : Type} (P : Q → Stmt Symbol Q (V × Option Symbol) 11)
variable (phase : ℕ → Q)
variable (table : ∀ j : Fin 6,
  P (phase j.val) = transferCode (src j) (dst j) (phase j.val) (phase (j.val + 1)) Option.isSome)

include table

theorem load_field (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (j : Fin 6) (r : ℕ)
    (bound : ∀ i, (column (f :: fs) i).length ≤ r) :
    Trace P r (localConfig (phase j.val) v (loading f fs j.val))
      (localConfig (phase (j.val + 1)) v (loading f fs (j.val + 1))) := by
  have path := transfer_field P (src j) (dst j) (src_ne_dst j j) (phase j.val) (phase (j.val + 1))
    Option.isSome (table j) v (loading f fs j.val) ((field f j).map some) none (column fs j)
    (by simp) (by
      intro s hs
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
      rfl) (by rfl) r (loading_bound f fs j.val r bound) (by
      have h := bound j
      simp only [column_cons, List.length_append, List.length_cons, List.length_map] at h
      simp; omega)
  simpa only [← List.map_reverse, loading_dst, Nat.lt_irrefl, ↓reduceIte, List.append_nil, loading_next] using path

/-- All six fields of the exact library frame are loaded, in order, by actual
finite stack-machine instructions. The columns below the top frame survive. -/
theorem load_frame (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (r : ℕ)
    (bound : ∀ j, (column (f :: fs) j).length ≤ r) :
    Trace P r (localConfig (phase 0) v (memory (f :: fs) (fun _ => [])))
      (localConfig (phase 6) v (memory fs (fun j => (field f j).reverse))) := by
  have walk (p : ℕ) (hp : p ≤ 6) :
      Trace P r (localConfig (phase 0) v (loading f fs 0)) (localConfig (phase p) v (loading f fs p)) := by
    induction p with
    | zero => exact .refl _ (loading_bound f fs 0 r bound)
    | succ p ih =>
        have first := ih (by omega)
        exact first.trans (load_field P phase table v f fs ⟨p, by omega⟩ r bound)
  simpa only [loading_zero, loading_six] using walk 6 (by omega)

end ComplexityOfGenerators.Simulation.SavitchMachine.Frames
