import ComplexityOfGenerators.Simulation.NativeEventTrace

namespace ComplexityOfGenerators.Machine
variable {E : Type} {C : Machine Unit Bool E}
    {parameter : E→Option (Fin C.symbols)→Bool} {Allowed : E→ℕ→Prop}
    {data : InputData Unit Bool} {bits : BitString} {events : List (E×ℕ)}
    {start finish last : Configuration C} {ticks : ℕ}

theorem NativeEventTrace.append (trace : C.NativeEventTrace parameter Allowed data bits events start finish)
    (tail : C.Steps data bits finish ticks last) (silent : last.output=finish.output) :
    C.NativeEventTrace parameter Allowed data bits events start last := by
  induction trace with
  | nil start finish t path output =>
      exact .nil _ _ _ (path.trans C tail) (silent.trans output)
  | cons e j events start before next write finish t path output allowed origin event unary rest ih =>
      exact .cons _ _ _ _ _ _ _ _ _ path output allowed origin event unary (ih tail silent)

end ComplexityOfGenerators.Machine
