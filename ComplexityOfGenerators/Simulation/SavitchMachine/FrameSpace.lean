import ComplexityOfGenerators.Simulation.SavitchMachine.FrameStore

/-! The library's Savitch invariant bounds the actual frame columns and the
temporary stacks used by the load/store programs. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Frames

open Complexity StackSpace

theorem field_length_le {f : Sav.Frm} {depth width : ℕ}
    (level : f.lvl.length ≤ depth) (codes : Sav.FrmSize width f) (j : Fin 6) :
    (field f j).length ≤ depth + width + 1 := by
  obtain ⟨hu, hv, hm⟩ := codes
  fin_cases j <;> simp [field] <;> omega

theorem column_length_le (fs : List Sav.Frm) (j : Fin 6) (size : ℕ)
    (bound : ∀ f ∈ fs, (field f j).length ≤ size) :
    (column fs j).length ≤ fs.length * (size + 1) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      have hf := bound f (by simp)
      have tail := ih (fun g hg => bound g (by simp [hg]))
      simp only [column_cons, List.length_append, List.length_map, List.length_cons]
      nlinarith

/-- A polynomial radius for each column, including its delimiters. -/
def frameRadius (depth width : ℕ) : ℕ := (depth + 1) * (depth + width + 2)

theorem column_bound {fs : List Sav.Frm} {depth width : ℕ}
    (size : Sav.StkSize depth width fs) (j : Fin 6) :
    (column fs j).length ≤ frameRadius depth width := by
  have fields : ∀ f ∈ fs, (field f j).length ≤ depth + width + 1 := by
    intro f hf
    obtain ⟨level, codes⟩ := size.mem_bound f hf
    exact field_length_le level codes j
  exact (column_length_le fs j _ fields).trans
    (Nat.mul_le_mul_right (depth + width + 2) size.length_le)

theorem load_frame_bounded {Q V : Type}
    (P : Q → Stmt Symbol Q (V × Option Symbol) 11) (phase : ℕ → Q)
    (table : ∀ j : Fin 6, P (phase j.val) =
      transferCode (src j) (dst j) (phase j.val) (phase (j.val + 1)) Option.isSome)
    (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (depth width : ℕ)
    (size : Sav.StkSize depth width (f :: fs)) :
    Trace P (frameRadius depth width)
      (localConfig (phase 0) v (memory (f :: fs) (fun _ => [])))
      (localConfig (phase 6) v (memory fs (fun j => (field f j).reverse))) :=
  load_frame P phase table v f fs _ (column_bound size)

theorem store_frame_bounded {Q V : Type}
    (P : Q → Stmt Symbol Q (V × Option Symbol) 11) (phase : ℕ → Q) (loop : Fin 6 → Q)
    (markTable : ∀ j : Fin 6,
      P (phase (j.val + 1)) = .push (src j) (fun _ => none) (.goto fun _ => loop j))
    (copyTable : ∀ j : Fin 6, P (loop j) =
      transferCode (dst j) (src j) (loop j) (phase j.val) (fun _ => true))
    (v : V) (f : Sav.Frm) (fs : List Sav.Frm) (depth width : ℕ)
    (size : Sav.StkSize depth width (f :: fs)) :
    Trace P (frameRadius depth width)
      (localConfig (phase 6) v (memory fs (fun j => (field f j).reverse)))
      (localConfig (phase 0) v (memory (f :: fs) (fun _ => []))) :=
  store_frame P phase loop markTable copyTable v f fs _ (column_bound size)

end ComplexityOfGenerators.Simulation.SavitchMachine.Frames
