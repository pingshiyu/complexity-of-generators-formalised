import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.Basic

namespace ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O) (parameter : F → Bool)

def advance (data : InputData Unit Bool) (c : Configuration (machine M parameter))
    (phase : Phase) (write : Option (Cell F M.symbols)) (move : Move) :
    Configuration (machine M parameter) :=
  (machine M parameter).stepConfiguration data c (control phase) (write.map (alphabet M))
    move .stay .stay .stay none

theorem advance_frame (data : InputData Unit Bool) (c : Configuration (machine M parameter))
    (phase write move) (bounds : ReadHeadBounds (machine M parameter) data c) :
    WorkFrame (machine M parameter) c (advance M parameter data c phase write move) :=
  ⟨rfl, by simp [advance, Machine.stepConfiguration], Nat.min_eq_left bounds.input,
    Nat.min_eq_left bounds.auxiliary, Nat.min_eq_left bounds.index⟩

theorem advance_path (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration (machine M parameter)) (phase next write move)
    (state : c.state=control phase)
    (table : transition M parameter phase (c.work c.workHead) =
      .step (control next) (write.map (alphabet M)) move .stay .stay .stay none) :
    (machine M parameter).Steps data bits c 1 (advance M parameter data c next write move) := by
  apply Machine.Steps.tail .refl
  apply (machine M parameter).next_step
  rw [state, machine_transition]
  exact table

structure State (data : InputData Unit Bool) (fixed : ℤ → F)
    (visited : Finset ℤ) (block : ℤ → Option IndexMark)
    (phase : Phase) (position : ℤ) (target : Configuration (machine M parameter)) : Prop where
  memory : Memory M fixed (fun _=>none) visited block target.work
  state : target.state=control phase
  head : target.workHead=position
  bounds : ReadHeadBounds (machine M parameter) data target

variable {M parameter} {data : InputData Unit Bool} {fixed : ℤ → F}
    {visited : Finset ℤ} {block : ℤ → Option IndexMark}
    {phase : Phase} {position : ℤ} {c : Configuration (machine M parameter)}

theorem State.silent (represented : State M parameter data fixed visited block phase position c)
    (bits : BitString) (next : Phase) (move : Move)
    (table : transition M parameter phase (c.work c.workHead) =
      .step (control next) none move .stay .stay .stay none) :
    ∃ d, State M parameter data fixed visited block next (move.onInt position) d ∧
      (machine M parameter).Steps data bits c 1 d ∧ WorkFrame (machine M parameter) c d := by
  let d := advance M parameter data c next none move
  refine ⟨d, ⟨represented.memory, rfl, ?_, ?_⟩,
    advance_path M parameter data bits c phase next none move represented.state table,
    advance_frame M parameter data c next none move represented.bounds⟩
  · change move.onInt c.workHead = _
    rw [represented.head]
  · exact represented.bounds.stepConfiguration (machine M parameter) data c _ _ _ _ _ _ _

theorem State.packetStep (represented : State M parameter data fixed visited block phase position c)
    (bits : BitString) (next : Phase) (mark : Option IndexMark) (move : Move)
    (table : transition M parameter phase (c.work c.workHead) =
      .step (control next) (some (alphabet M {read M (c.work c.workHead) with packet := mark}))
        move .stay .stay .stay none) :
    ∃ d, State M parameter data fixed visited (Function.update block position mark)
        next (move.onInt position) d ∧
      (machine M parameter).Steps data bits c 1 d ∧ WorkFrame (machine M parameter) c d := by
  let cell := {read M (c.work c.workHead) with packet := mark}
  let d := advance M parameter data c next (some cell) move
  refine ⟨d, ⟨?_, rfl, ?_, ?_⟩,
    advance_path M parameter data bits c phase next (some cell) move represented.state table,
    advance_frame M parameter data c next (some cell) move represented.bounds⟩
  · change Memory M fixed (fun _=>none) visited (Function.update block position mark)
      (Function.update c.work c.workHead (some (alphabet M cell)))
    dsimp only [cell]
    rw [represented.head]
    exact represented.memory.packet_write M position mark
  · change move.onInt c.workHead = _
    rw [represented.head]
  · exact represented.bounds.stepConfiguration (machine M parameter) data c _ _ _ _ _ _ _

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
