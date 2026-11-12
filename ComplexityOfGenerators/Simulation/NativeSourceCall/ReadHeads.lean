import ComplexityOfGenerators.Simulation.NativeSourceCall.Basic

/-! The source has empty ordinary and auxiliary input and a virtual index.
Consequently all three physical read-only heads belong to the suspended caller
and are framed throughout every native call path. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem transition_readOnly (phase : Phase O M.states M.symbols) (raw)
    (next write work input auxiliary index emit)
    (action : transition (F := F) M phase raw=.step next write work input auxiliary index emit) :
    input=.stay ∧ auxiliary=.stay ∧ index=.stay := by
  cases phase <;> simp only [transition] at action <;>
    repeat' first | split at action | cases h : (read M raw).packet <;> simp only [h] at action
  all_goals first | cases action; exact ⟨rfl,rfl,rfl⟩ | contradiction

theorem steps_readHeads (data : InputData Unit Bool) (bits : BitString)
    {c d : Configuration (machine (F := F) M)} {ticks : ℕ}
    (path : (machine M).Steps data bits c ticks d) (bounds : ReadHeadBounds (machine M) data c) :
    ReadHeadBounds (machine M) data d ∧ d.inputHead=c.inputHead ∧
      d.auxiliaryHead=c.auxiliaryHead ∧ d.indexHead=c.indexHead := by
  induction path with
  | refl => exact ⟨bounds,rfl,rfl,rfl⟩
  | @tail ticks current next path edge ih =>
      obtain ⟨currentBounds,inputEqual,auxiliaryEqual,indexEqual⟩ := ih
      cases action : (machine M).transition current.state data.input[current.inputHead]?
          data.auxiliary[current.auxiliaryHead]?
          (if current.indexHead<data.index then some () else none) (current.work current.workHead) with
      | accept => simp [Machine.next,action] at edge
      | reject => simp [Machine.next,action] at edge
      | readRandom no yes =>
          cases lookup : bits[current.randomHead]? with
          | none => simp [Machine.next,action,lookup] at edge
          | some bit =>
              simp only [Machine.next,action,lookup,RunState.running.injEq] at edge
              subst next
              exact ⟨⟨currentBounds.input,currentBounds.auxiliary,currentBounds.index⟩,inputEqual,auxiliaryEqual,indexEqual⟩
      | step state write work input auxiliary index emit =>
          have stationary := transition_readOnly M ((control M).symm current.state) (current.work current.workHead)
            state write work input auxiliary index emit (by simpa [machine,routine,Routine.machine] using action)
          obtain ⟨rfl,rfl,rfl⟩ := stationary
          rw [(machine M).next_step data bits current state write work .stay .stay .stay emit action] at edge
          cases edge
          refine ⟨currentBounds.stepConfiguration (machine M) data current _ _ _ _ _ _ _,?_,?_,?_⟩
          · exact (Nat.min_eq_left currentBounds.input).trans inputEqual
          · exact (Nat.min_eq_left currentBounds.auxiliary).trans auxiliaryEqual
          · exact (Nat.min_eq_left currentBounds.index).trans indexEqual

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
