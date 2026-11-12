import ComplexityOfGenerators.Simulation.NativeSourceCall.State
import Mathlib.Data.Int.Interval

/-! Linear cleanup of the source's connected visited interval. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

variable {M} {data : InputData Unit Bool} {fixed : ℤ → F} {source : ℤ → Option (Fin M.symbols)}
    {visited : Finset ℤ} {block : ℤ → Option IndexMark} {phase : Phase O M.states M.symbols}
    {position : ℤ} {c : Configuration (machine (F := F) M)}

theorem State.eraseStep (represented : State M data fixed source visited block phase position c)
    (bits : BitString) (next : Phase O M.states M.symbols)
    (table : transition M phase (c.work c.workHead) =
      .step (control M next) (some (alphabet M {read M (c.work c.workHead) with source := none, visited := false}))
        .right .stay .stay .stay none) :
    ∃ d, State M data fixed (Function.update source position none) (visited.erase position) block
      next (position+1) d ∧ (machine M).Steps data bits c 1 d ∧ WorkFrame (machine M) c d := by
  let cell : Cell F M.symbols := {read M (c.work c.workHead) with source := none, visited := false}
  let d := advance M data c next (some cell) .right
  refine ⟨d, ⟨?_,rfl,?_,advance_bounds M data c next (some cell) .right none represented.bounds⟩,
    advance_path M data bits c phase next (some cell) .right none represented.state table,
    advance_frame M data c next (some cell) .right represented.bounds⟩
  · change Memory M fixed (Function.update source position none) (visited.erase position) block
      (Function.update c.work c.workHead (some (alphabet M cell)))
    dsimp only [cell]
    rw [represented.head]
    exact represented.memory.erase_write M position
  · simpa only [d,advance_head,represented.head,Move.onInt]

variable (M)

theorem erase_interval (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (count : ℕ) (lo : ℤ) (source : ℤ → Option (Fin M.symbols))
    (blank : ∀ x, x∉Finset.Ico lo (lo+count) → source x=none)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source (Finset.Ico lo (lo+count)) (fun _ => none) .cleanupRight lo c) :
    ∃ d, State M data fixed (fun _ => none) ∅ (fun _ => none) .cleanupOrigin (lo+count-1) d ∧
      (machine M).Steps data bits c (count+1) d ∧ WorkFrame (machine M) c d := by
  induction count generalizing lo source c with
  | zero =>
      have empty : Finset.Ico lo (lo+(0 : ℕ)) = ∅ := by simp
      have sourceEmpty : source = fun _ => none := by funext x; exact blank x (by simp)
      have mark : (read M (c.work c.workHead)).visited=false := by
        rw [represented.head,represented.memory]
        simp
      obtain ⟨d,state,path,frame⟩ := represented.silent bits .cleanupOrigin .left (by
        simp only [transition,mark,Bool.false_eq_true,↓reduceIte])
      refine ⟨d,?_,path,frame⟩
      simpa only [sourceEmpty,Move.onInt,Nat.cast_zero,add_zero,Finset.Ico_self] using state
  | succ count ih =>
      have mark : (read M (c.work c.workHead)).visited=true := by
        rw [represented.head,represented.memory]
        simp only [Finset.mem_Ico,le_refl,true_and,decide_eq_true_eq]
        omega
      obtain ⟨next,state,path,frame⟩ := represented.eraseStep bits .cleanupRight (by
        simp only [transition,mark,↓reduceIte])
      have eraseSet : (Finset.Ico lo (lo+((count+1 : ℕ) : ℤ))).erase lo =
          Finset.Ico (lo+1) ((lo+1)+count) := by
        ext x
        simp only [Finset.mem_erase,Finset.mem_Ico]
        omega
      have ready : State M data fixed (Function.update source lo none)
          (Finset.Ico (lo+1) ((lo+1)+count)) (fun _ => none) .cleanupRight (lo+1) next := by
        rwa [eraseSet] at state
      have remainingBlank : ∀ x, x∉Finset.Ico (lo+1) ((lo+1)+count) →
          Function.update source lo none x=none := by
        intro x outside
        by_cases same : x=lo
        · subst x; simp
        · rw [Function.update_of_ne same]
          apply blank x
          simp only [Finset.mem_Ico] at outside ⊢
          omega
      obtain ⟨d,done,rest,restFrame⟩ := ih (lo+1) (Function.update source lo none) remainingBlank next ready
      refine ⟨d,?_,?_,frame.trans (machine M) restFrame⟩
      · convert done using 1 <;> push_cast <;> omega
      · convert path.trans (machine M) rest using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
