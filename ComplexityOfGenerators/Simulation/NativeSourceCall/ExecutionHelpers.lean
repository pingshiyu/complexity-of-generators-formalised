import ComplexityOfGenerators.Simulation.NativeSourceCall.Basic

/-! Primitive execution helpers for the native call table. These lemmas count
real native transitions and retain arbitrary suspended read-only heads. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

def advance (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase : Phase O M.states M.symbols) (write : Option (Cell F M.symbols))
    (move : Move) (emit : Option O := none) : Configuration (machine (F := F) M) :=
  (machine M).stepConfiguration data c (control M phase) (write.map (alphabet M)) move .stay .stay .stay emit

@[simp] theorem advance_state (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase write move emit) : (advance M data c phase write move emit).state = control M phase := rfl
@[simp] theorem advance_head (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase write move emit) : (advance M data c phase write move emit).workHead = move.onInt c.workHead := rfl
@[simp] theorem advance_random (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase write move emit) : (advance M data c phase write move emit).randomHead = c.randomHead := rfl

@[simp] theorem advance_work_none (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase move emit) : (advance M data c phase none move emit).work = c.work := rfl
@[simp] theorem advance_work_some (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase cell move emit) : (advance M data c phase (some cell) move emit).work =
      Function.update c.work c.workHead (some (alphabet M cell)) := rfl

theorem advance_frame (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase write move) (bounds : ReadHeadBounds (machine M) data c) :
    WorkFrame (machine M) c (advance M data c phase write move) :=
  ⟨rfl, by simp [advance, Machine.stepConfiguration], Nat.min_eq_left bounds.input,
    Nat.min_eq_left bounds.auxiliary, Nat.min_eq_left bounds.index⟩

theorem advance_bounds (data : InputData Unit Bool) (c : Configuration (machine (F := F) M))
    (phase write move emit) (bounds : ReadHeadBounds (machine M) data c) :
    ReadHeadBounds (machine M) data (advance M data c phase write move emit) :=
  bounds.stepConfiguration (machine M) data c _ _ _ _ _ _ _

theorem advance_path (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration (machine (F := F) M)) (phase next write move emit)
    (state : c.state=control M phase)
    (table : transition M phase (c.work c.workHead) =
      .step (control M next) (write.map (alphabet M)) move .stay .stay .stay emit) :
    (machine M).Steps data bits c 1 (advance M data c next write move emit) := by
  apply Machine.Steps.tail .refl
  apply (machine M).next_step
  rw [state, machine_transition]
  exact table

/-- Any complete call path preserves the fixed track, including portions of
that track lying arbitrarily far from the source's current work head. -/
theorem steps_fixed (data : InputData Unit Bool) (bits : BitString)
    {c d : Configuration (machine (F := F) M)} {ticks : ℕ}
    (path : (machine M).Steps data bits c ticks d) :
    ∀ position, (read M (d.work position)).fixed = (read M (c.work position)).fixed := by
  induction path with
  | refl => intro position; rfl
  | @tail ticks current next path edge ih =>
      intro position
      have one : (read M (next.work position)).fixed = (read M (current.work position)).fixed := by
        cases action : (machine M).transition current.state data.input[current.inputHead]?
            data.auxiliary[current.auxiliaryHead]?
            (if current.indexHead<data.index then some () else none) (current.work current.workHead) with
        | accept => simp [Machine.next, action] at edge
        | reject => simp [Machine.next, action] at edge
        | readRandom no yes =>
            cases lookup : bits[current.randomHead]? with
            | none => simp [Machine.next, action, lookup] at edge
            | some bit =>
                simp only [Machine.next, action, lookup, RunState.running.injEq] at edge
                subst next
                rfl
        | step state write work input auxiliary index emit =>
            rw [(machine M).next_step data bits current state write work input auxiliary index emit action] at edge
            cases edge
            cases write with
            | none => rfl
            | some symbol =>
                change (read M ((Function.update current.work current.workHead (some symbol)) position)).fixed = _
                by_cases same : position=current.workHead
                · subst position
                  rw [Function.update_self]
                  apply transition_fixed M ((control M).symm current.state) (current.work current.workHead)
                    state (some symbol) work input auxiliary index emit ?_ symbol (by simp)
                  simpa [machine, routine, Routine.machine] using action
                · rw [Function.update_of_ne same]
      exact one.trans (ih position)

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
