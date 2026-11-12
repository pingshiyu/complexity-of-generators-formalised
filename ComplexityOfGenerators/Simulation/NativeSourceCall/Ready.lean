import ComplexityOfGenerators.Simulation.NativeSourceCall.State

/-! A source snapshot may be suspended inside a larger native computation.
The unread random tape is a suffix and already-emitted output is a prefix;
neither is copied into the work tape or the bounded index packet. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

structure Ready (data : InputData Unit Bool) (fixed : ℤ → F) (length offset : ℕ) (output : List O)
    (source : Configuration M) (target : Configuration (machine (F := F) M)) : Prop where
  represented : State M data fixed source.work source.visited
    (packet length source.indexHead source.workHead) (.source source.state) source.workHead target
  index : source.indexHead≤length
  input : source.inputHead=0
  auxiliary : source.auxiliaryHead=0
  geometry : M.TapeGeometry source
  random : target.randomHead=offset+source.randomHead
  output : target.output=output++source.output

theorem ready_initial (data : InputData Unit Bool) (fixed : ℤ → F) (length : ℕ)
    (target : Configuration (machine (F := F) M))
    (state : State M data fixed (fun _ => none) {0} (packet length 0 0) (.source M.initial) 0 target) :
    Ready M data fixed length target.randomHead target.output M.initialConfiguration target := by
  exact ⟨state,Nat.zero_le _,rfl,rfl,M.initialConfiguration_geometry,by simp [Machine.initialConfiguration],
    by simp [Machine.initialConfiguration]⟩

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
