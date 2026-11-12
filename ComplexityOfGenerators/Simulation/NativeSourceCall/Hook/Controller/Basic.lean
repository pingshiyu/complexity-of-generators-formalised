import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Basic

/-! A suspended native controller uses the fixed alphabet track. Its output
consists of control events and is distinct from the physical source output.
The actual native visited set may grow during source calls and is deliberately
absent from this correspondence: controller scan time depends on its own heads. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

structure ControllerReady (data : InputData Unit Bool) (origin : Bool)
    (source : Configuration C) (target : Configuration (machine C M parameter start)) : Prop where
  memory : ParameterInitialisation.BlankMemory M source.work origin target.work
  state : target.state=control C M (.controller source.state)
  head : target.workHead=source.workHead
  input : target.inputHead=source.inputHead
  auxiliary : target.auxiliaryHead=source.auxiliaryHead
  index : target.indexHead=source.indexHead
  random : target.randomHead=source.randomHead
  bounds : ReadHeadBounds C data source

theorem controller_memory_write (fixed : ℤ → Fixed C) (origin : Bool)
    (memory : ℤ → Option (Fin (Fintype.card (Work C M))))
    (represented : ParameterInitialisation.BlankMemory M fixed origin memory)
    (position : ℤ) (symbol : Fin C.symbols) :
    ParameterInitialisation.BlankMemory M (Function.update fixed position (some symbol)) origin
      (Function.update memory position (some (alphabet M {read M (memory position) with fixed:=some symbol}))) := by
  intro x
  by_cases same : x=position
  · subst x
    simp only [Function.update_self,read_write,represented position]
  · simp only [Function.update_of_ne same,represented x]

/-- Output is append-only at the native instruction level. -/
theorem controller_next_output (data : InputData Unit Bool) (bits : BitString)
    (c d : Configuration C) (edge : C.next data bits c=.running d) : ∃ extra, d.output=c.output++extra := by
  cases action : C.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [Machine.next,action] at edge
  | reject => simp [Machine.next,action] at edge
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next,action,lookup] at edge
      | some bit =>
          simp only [Machine.next,action,lookup,RunState.running.injEq] at edge
          subst d
          exact ⟨[],by simp⟩
  | step state write work input auxiliary index emit =>
      rw [C.next_step data bits c state write work input auxiliary index emit action] at edge
      cases edge
      cases emit with
      | none => exact ⟨[],by simp [Machine.stepConfiguration]⟩
      | some event => exact ⟨[event],rfl⟩

theorem controller_path_output (data : InputData Unit Bool) (bits : BitString)
    {c d : Configuration C} {ticks : ℕ} (path : C.Steps data bits c ticks d) :
    ∃ extra, d.output=c.output++extra := by
  induction path with
  | refl => exact ⟨[],by simp⟩
  | @tail ticks current next path edge ih =>
      obtain ⟨first,firstEqual⟩ := ih
      obtain ⟨last,lastEqual⟩ := controller_next_output C data bits current next edge
      exact ⟨first++last,by rw [lastEqual,firstEqual,List.append_assoc]⟩

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
