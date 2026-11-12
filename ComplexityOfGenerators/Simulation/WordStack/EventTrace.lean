import ComplexityOfGenerators.Simulation.WordStack.Commands

/-! Finite controller paths with explicit call-event sites. Ordinary segments
are actual primitive paths with unchanged output; event sites expose their
selected empty register and exported positive unary factor. -/
namespace ComplexityOfGenerators.Simulation.WordStack
namespace Program
set_option backward.isDefEq.respectTransparency false
variable {Q Q' S E : Type} {k : ℕ} (P : Program Q S E k)

inductive EventTrace (slot exported : Fin k) (symbol : S) (Allowed : E→ℕ→Prop) (n : ℕ) (bits : BitString) :
    List (E×ℕ) → Configuration Q S E k → Configuration Q S E k → Prop
  | nil (start finish ticks) (path : P.Steps n bits start ticks finish)
      (silent : finish.output=start.output) : EventTrace slot exported symbol Allowed n bits [] start finish
  | cons (e j parts start before next finish ticks)
      (segment : P.Steps n bits start ticks before) (silent : before.output=start.output)
      (allowed : Allowed e j) (selected : P.select before.state=slot) (empty : before.store slot=[])
      (parameter : before.store exported=List.replicate (j-1) symbol)
      (event : P.instruction n before=.step next .stay .stay (some e))
      (rest : EventTrace slot exported symbol Allowed n bits parts
        (P.advance n before next .stay .stay (some e)) finish) :
      EventTrace slot exported symbol Allowed n bits ((e,j)::parts) start finish

variable {P} {slot exported : Fin k} {symbol : S} {Allowed : E→ℕ→Prop} {n : ℕ} {bits : BitString}
    {parts : List (E×ℕ)} {start finish : Configuration Q S E k}

theorem EventTrace.prepend (trace : P.EventTrace slot exported symbol Allowed n bits parts start finish)
    {earlier : Configuration Q S E k} {ticks : ℕ}
    (segment : P.Steps n bits earlier ticks start) (silent : start.output=earlier.output) :
    P.EventTrace slot exported symbol Allowed n bits parts earlier finish := by
  cases trace with
  | nil start finish t path output => exact .nil _ _ _ (segment.trans P path) (output.trans silent)
  | cons e j parts start before next finish t path output allowed selected empty parameter event rest =>
      exact .cons _ _ _ _ _ _ _ _ (segment.trans P path) (output.trans silent)
        allowed selected empty parameter event rest

theorem EventTrace.steps (trace : P.EventTrace slot exported symbol Allowed n bits parts start finish) :
    ∃ ticks, P.Steps n bits start ticks finish := by
  induction trace with
  | nil start finish ticks path silent => exact ⟨ticks,path⟩
  | cons e j parts start before next finish ticks segment silent allowed selected empty parameter event rest ih =>
      obtain ⟨t,path⟩ := ih
      exact ⟨ticks+1+t,(segment.trans P (Steps.single P n bits before next .stay .stay (some e) event)).trans P path⟩

theorem EventTrace.embeds {T : Program Q' S E k} {f : Q→Q'}
    (trace : P.EventTrace slot exported symbol Allowed n bits parts start finish) (embedding : P.Embeds T f) :
    T.EventTrace slot exported symbol Allowed n bits parts (start.mapState f) (finish.mapState f) := by
  induction trace with
  | nil start finish ticks path silent =>
      exact .nil _ _ ticks (embedding.steps P path) silent
  | cons e j parts start before next finish ticks segment silent allowed selected empty parameter event rest ih =>
      refine .cons e j parts _ _ (f next) _ ticks (embedding.steps P segment) silent allowed ?_ empty parameter ?_ ?_
      · exact (embedding.select before.state).trans selected
      · simp only [instruction,Configuration.mapState,embedding.select]
        exact embedding.step _ _ _ _ _ _ _ event
      · rwa [embedding.advance P n before next .stay .stay (some e)]

theorem Embeds.trans {Q'' : Type} {T : Program Q' S E k} {U : Program Q'' S E k}
    {f : Q→Q'} {g : Q'→Q''} (first : P.Embeds T f) (second : T.Embeds U g) :
    P.Embeds U (g∘f) where
  select q := (second.select (f q)).trans (first.select q)
  step q cell input next action index emit table :=
    second.step _ _ _ _ _ _ _ (first.step _ _ _ _ _ _ _ table)
  random q cell input no yes table := second.random _ _ _ _ _ (first.random _ _ _ _ _ table)

end Program
end ComplexityOfGenerators.Simulation.WordStack
