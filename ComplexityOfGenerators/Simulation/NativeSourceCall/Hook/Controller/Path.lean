import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Step

/-! A bounded native controller segment with no events is copied with exactly
its own native running time, preserving any preceding source output. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem controller_path (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source finishSource : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target) (ticks : ℕ)
    (path : C.Steps data bits source ticks finishSource) (noEvent : finishSource.output=source.output) :
    ∃ finishTarget, ControllerReady C M parameter start data origin finishSource finishTarget ∧
      (machine C M parameter start).Steps data bits target ticks finishTarget ∧ finishTarget.output=target.output := by
  induction path generalizing target with
  | refl => exact ⟨target,ready,.refl,rfl⟩
  | @tail ticks current next path edge ih =>
      obtain ⟨first,firstEqual⟩ := controller_path_output C data bits path
      obtain ⟨last,lastEqual⟩ := controller_next_output C data bits current next edge
      have empty : first=[] := by
        have lengths := congrArg List.length noEvent
        rw [lastEqual,firstEqual] at lengths
        simp only [List.length_append] at lengths
        apply List.length_eq_zero_iff.mp
        omega
      have currentEqual : current.output=source.output := by simpa only [empty,List.append_nil] using firstEqual
      have nextEqual : next.output=current.output := noEvent.trans currentEqual.symm
      obtain ⟨middle,middleReady,replayed,output⟩ := ih target ready currentEqual
      obtain ⟨finish,finishReady,final,finalOutput⟩ := controller_next C M parameter start data bits origin current next middle middleReady edge nextEqual
      exact ⟨finish,finishReady,replayed.trans (machine C M parameter start) final,finalOutput.trans output⟩

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
