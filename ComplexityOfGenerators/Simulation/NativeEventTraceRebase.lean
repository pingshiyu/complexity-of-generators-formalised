import ComplexityOfGenerators.Simulation.NativeEventTrace
import ComplexityOfGenerators.Foundations.RandomCursorRebase

namespace ComplexityOfGenerators.Machine
set_option backward.isDefEq.respectTransparency false
variable {E : Type} {C : Machine Unit Bool E}
    {parameter : E→Option (Fin C.symbols)→Bool} {Allowed : E→ℕ→Prop}
    {data : InputData Unit Bool} {bits : BitString} {events : List (E×ℕ)}
    {start finish : Configuration C}

/-- A deterministic controller suffix can be resumed at the cursor left by
an inserted original-source call, with its event parameters unchanged. -/
theorem NativeEventTrace.rebase_random
    (trace : C.NativeEventTrace parameter Allowed data bits events start finish)
    (stable : finish.randomHead=start.randomHead) (otherBits : BitString) (cursor : ℕ) :
    C.NativeEventTrace parameter Allowed data otherBits events
      (C.rebaseRandom start cursor) (C.rebaseRandom finish cursor) := by
  induction trace with
  | nil start finish ticks path silent =>
      exact .nil _ _ ticks (path.rebase_random C stable otherBits cursor) silent
  | cons e j events start before next write finish ticks segment silent allowed origin event unary rest ih =>
      have beforeMono := segment.randomHead_mono C
      obtain ⟨t,restPath⟩ := rest.steps
      have afterMono := restPath.randomHead_mono C
      change before.randomHead≤finish.randomHead at afterMono
      have beforeStable : before.randomHead=start.randomHead := by omega
      have restStable : finish.randomHead=
          (C.stepConfiguration data before next write .stay .stay .stay .stay (some e)).randomHead := by
        change finish.randomHead=before.randomHead
        omega
      have rebaseAdvance : C.stepConfiguration data (C.rebaseRandom before cursor) next write
          .stay .stay .stay .stay (some e) =
          C.rebaseRandom (C.stepConfiguration data before next write .stay .stay .stay .stay (some e)) cursor := by
        cases write <;> rfl
      refine .cons e j events _ (C.rebaseRandom before cursor) next write _ ticks
        (segment.rebase_random C beforeStable otherBits cursor) silent allowed origin event ?_ ?_
      · intro p
        rw [rebaseAdvance]
        exact unary p
      · rw [rebaseAdvance]
        exact ih restStable

end ComplexityOfGenerators.Machine
