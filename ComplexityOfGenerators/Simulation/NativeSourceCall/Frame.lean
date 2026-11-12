import ComplexityOfGenerators.Simulation.NativeSourceCall.State

/-! Physical source calls append to the existing output and consume only their
own random bits; suspended read-only heads keep their actual positions. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

structure Frame (emitted : List O) (c d : Configuration (machine (F := F) M)) : Prop where
  random : d.randomHead=c.randomHead
  input : d.inputHead=c.inputHead
  auxiliary : d.auxiliaryHead=c.auxiliaryHead
  index : d.indexHead=c.indexHead
  output : d.output=c.output++emitted

variable {M} {c d e : Configuration (machine (F := F) M)} {first second : List O}

theorem Frame.ofWork (frame : WorkFrame (machine M) c d) : Frame M [] c d :=
  ⟨frame.random,frame.input,frame.auxiliary,frame.index,by simpa using frame.output⟩

theorem Frame.trans (left : Frame M first c d) (right : Frame M second d e) :
    Frame M (first++second) c e := by
  refine ⟨right.random.trans left.random,right.input.trans left.input,
    right.auxiliary.trans left.auxiliary,right.index.trans left.index,?_⟩
  rw [right.output,left.output,List.append_assoc]

theorem Frame.beforeWork (left : WorkFrame (machine M) c d) (right : Frame M second d e) :
    Frame M second c e := by
  simpa using (Frame.ofWork left).trans right

theorem Frame.afterWork (left : Frame M first c d) (right : WorkFrame (machine M) d e) :
    Frame M first c e := by
  simpa using left.trans (Frame.ofWork right)

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
