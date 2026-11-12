import ComplexityOfGenerators.Simulation.NativeSourceCall.ExecutionHelpers
import ComplexityOfGenerators.Simulation.NativeSourceCall.Memory

/-! Packaged invariants for actual native source-call instruction paths. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

structure State (data : InputData Unit Bool) (fixed : ℤ → F)
    (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ) (block : ℤ → Option IndexMark)
    (phase : Phase O M.states M.symbols) (position : ℤ) (target : Configuration (machine (F := F) M)) : Prop where
  memory : Memory M fixed source visited block target.work
  state : target.state=control M phase
  head : target.workHead=position
  bounds : ReadHeadBounds (machine M) data target

variable {M} {data : InputData Unit Bool} {fixed : ℤ → F} {source : ℤ → Option (Fin M.symbols)}
    {visited : Finset ℤ} {block : ℤ → Option IndexMark}
    {phase : Phase O M.states M.symbols} {position : ℤ}
    {c : Configuration (machine (F := F) M)}

theorem State.silent (represented : State M data fixed source visited block phase position c)
    (bits : BitString) (next : Phase O M.states M.symbols) (move : Move)
    (table : transition M phase (c.work c.workHead) =
      .step (control M next) none move .stay .stay .stay none) :
    ∃ d, State M data fixed source visited block next (move.onInt position) d ∧
      (machine M).Steps data bits c 1 d ∧ WorkFrame (machine M) c d := by
  let d := advance M data c next none move
  refine ⟨d, ⟨?_, rfl, ?_, advance_bounds M data c next none move none represented.bounds⟩,
    advance_path M data bits c phase next none move none represented.state table,
    advance_frame M data c next none move represented.bounds⟩
  · exact represented.memory
  · simpa only [d, advance_head, represented.head]

theorem State.packetStep (represented : State M data fixed source visited block phase position c)
    (bits : BitString) (next : Phase O M.states M.symbols) (mark : Option IndexMark) (move : Move)
    (table : transition M phase (c.work c.workHead) =
      .step (control M next) (some (alphabet M {read M (c.work c.workHead) with packet := mark}))
        move .stay .stay .stay none) :
    ∃ d, State M data fixed source visited (Function.update block position mark) next (move.onInt position) d ∧
      (machine M).Steps data bits c 1 d ∧ WorkFrame (machine M) c d := by
  let cell := {read M (c.work c.workHead) with packet := mark}
  let d := advance M data c next (some cell) move
  refine ⟨d, ⟨?_, rfl, ?_, advance_bounds M data c next (some cell) move none represented.bounds⟩,
    advance_path M data bits c phase next (some cell) move none represented.state table,
    advance_frame M data c next (some cell) move represented.bounds⟩
  · change Memory M fixed source visited (Function.update block position mark)
      (Function.update c.work c.workHead (some (alphabet M cell)))
    dsimp only [cell]
    rw [represented.head]
    exact represented.memory.packet_write M position mark
  · simpa only [d, advance_head, represented.head]

theorem State.visitStep (represented : State M data fixed source visited block phase position c)
    (bits : BitString) (next : Phase O M.states M.symbols)
    (table : transition M phase (c.work c.workHead) =
      .step (control M next) (some (alphabet M {read M (c.work c.workHead) with visited := true}))
        .stay .stay .stay .stay none) :
    ∃ d, State M data fixed source (insert position visited) block next position d ∧
      (machine M).Steps data bits c 1 d ∧ WorkFrame (machine M) c d := by
  let cell := {read M (c.work c.workHead) with visited := true}
  let d := advance M data c next (some cell) .stay
  refine ⟨d, ⟨?_, rfl, ?_, advance_bounds M data c next (some cell) .stay none represented.bounds⟩,
    advance_path M data bits c phase next (some cell) .stay none represented.state table,
    advance_frame M data c next (some cell) .stay represented.bounds⟩
  · change Memory M fixed source (insert position visited) block
      (Function.update c.work c.workHead (some (alphabet M cell)))
    dsimp only [cell]
    rw [represented.head]
    exact represented.memory.visit_write M position
  · simpa only [d, advance_head, represented.head, Move.onInt]

/-- A finite scan keeps its memory relation and the suspended context. -/
theorem State.scan (represented : State M data fixed source visited block phase position c)
    (bits : BitString) (steps : ℕ) (direction : Move) (endPosition : ℤ)
    (coordinates : ℕ → ℤ) (initial : coordinates 0=position) (final : coordinates steps=endPosition)
    (moves : ∀ t, t<steps → direction.onInt (coordinates t)=coordinates (t+1))
    (table : ∀ t, t<steps → ∀ input auxiliary index,
      (machine M).transition (control M phase) input auxiliary index (c.work (coordinates t)) =
        .step (control M phase) none direction .stay .stay .stay none) :
    ∃ d, State M data fixed source visited block phase endPosition d ∧
      (machine M).Steps data bits c steps d ∧ WorkFrame (machine M) c d := by
  obtain ⟨d, summary, path, _⟩ := tapeScan_path (machine M) data bits c (control M phase)
    coordinates (fun _ => direction) steps represented.bounds represented.state
    (represented.head.trans initial.symm) moves table
  refine ⟨d, ⟨?_, summary.state.trans represented.state, summary.head.trans final,
    summary.readHeadBounds (machine M) represented.bounds⟩, path, summary.workFrame (machine M)⟩
  rw [summary.memory]
  exact represented.memory

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
