import ComplexityOfGenerators.Simulation.WorkSteps

/-! Actual single-tape controller traces split at source-call events. The
parameter is checked on the work tape after the controller's event step. -/
namespace ComplexityOfGenerators.Machine
variable {E : Type} (C : Machine Unit Bool E)
    (parameter : E→Option (Fin C.symbols)→Bool) (Allowed : E→ℕ→Prop)

inductive NativeEventTrace (data : InputData Unit Bool) (bits : BitString) :
    List (E×ℕ) → Configuration C → Configuration C → Prop
  | nil (start finish ticks) (path : C.Steps data bits start ticks finish)
      (silent : finish.output=start.output) : NativeEventTrace data bits [] start finish
  | cons (e j parts start before next write finish ticks)
      (segment : C.Steps data bits start ticks before) (silent : before.output=start.output)
      (allowed : Allowed e j) (origin : before.workHead=0)
      (event : C.transition before.state data.input[before.inputHead]? data.auxiliary[before.auxiliaryHead]?
        (if before.indexHead<data.index then some () else none) (before.work before.workHead)=
          .step next write .stay .stay .stay .stay (some e))
      (unary : ∀ p : ℕ, parameter e
        ((C.stepConfiguration data before next write .stay .stay .stay .stay (some e)).work p)=decide (p<j))
      (rest : NativeEventTrace data bits parts
        (C.stepConfiguration data before next write .stay .stay .stay .stay (some e)) finish) :
      NativeEventTrace data bits ((e,j)::parts) start finish

variable {C parameter Allowed} {data : InputData Unit Bool} {bits : BitString}
    {parts : List (E×ℕ)} {start finish : Configuration C}

theorem NativeEventTrace.prepend (trace : C.NativeEventTrace parameter Allowed data bits parts start finish)
    {earlier : Configuration C} {ticks : ℕ} (segment : C.Steps data bits earlier ticks start)
    (silent : start.output=earlier.output) :
    C.NativeEventTrace parameter Allowed data bits parts earlier finish := by
  cases trace with
  | nil start finish t path output => exact .nil _ _ _ (segment.trans C path) (output.trans silent)
  | cons e j parts start before next write finish t path output allowed origin event unary rest =>
      exact .cons _ _ _ _ _ _ _ _ _ (segment.trans C path) (output.trans silent)
        allowed origin event unary rest

theorem NativeEventTrace.steps (trace : C.NativeEventTrace parameter Allowed data bits parts start finish) :
    ∃ ticks, C.Steps data bits start ticks finish := by
  induction trace with
  | nil start finish ticks path silent => exact ⟨ticks,path⟩
  | cons e j parts start before next write finish ticks segment silent allowed origin event unary rest ih =>
      obtain ⟨t,path⟩ := ih
      have edge : C.Steps data bits before 1
          (C.stepConfiguration data before next write .stay .stay .stay .stay (some e)) :=
        .tail .refl (C.next_step _ _ _ _ _ _ _ _ _ _ event)
      exact ⟨ticks+1+t,(segment.trans C edge).trans C path⟩

end ComplexityOfGenerators.Machine
