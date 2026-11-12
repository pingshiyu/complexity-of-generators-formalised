import ComplexityOfGenerators.Simulation.WordStack.EventTrace

namespace ComplexityOfGenerators.Simulation.WordStack.Program
set_option backward.isDefEq.respectTransparency false
variable {Q Q' S E : Type} {k : ℕ} (P : Program Q S E k)

def EventReturns (slot exported : Fin k) (symbol : S) (Allowed : E→ℕ→Prop) (n : ℕ) (bits : BitString)
    (events : List (E×ℕ)) (start finish : Memory S E k) : Prop :=
  ∃ q, P.EventTrace slot exported symbol Allowed n bits events (start.at P.initial) (finish.at q) ∧
    P.instruction n (finish.at q)=.accept

variable {P} {slot exported : Fin k} {symbol : S} {Allowed : E→ℕ→Prop}
    {n : ℕ} {bits : BitString} {events : List (E×ℕ)} {start finish : Memory S E k}

theorem Returns.event_nil {ticks : ℕ} (run : P.Returns n bits start ticks finish)
    (silent : finish.output=start.output) :
    P.EventReturns slot exported symbol Allowed n bits [] start finish := by
  obtain ⟨q,path,terminal⟩ := run
  exact ⟨q,.nil _ _ _ path silent,terminal⟩

theorem EventReturns.sequence_silent_before {T : Program Q' S E k} {middle : Memory S E k} {ticks : ℕ}
    (right : T.EventReturns slot exported symbol Allowed n bits events middle finish)
    (left : P.Returns n bits start ticks middle) (bounded : start.indexHead≤n)
    (silent : middle.output=start.output) :
    (P.sequence T).EventReturns slot exported symbol Allowed n bits events start finish := by
  obtain ⟨q,path,terminal⟩ := left
  obtain ⟨r,trace,halt⟩ := right
  have first := (P.sequence_left T).steps P path
  have transfer : (P.sequence T).Steps n bits (middle.at (.inl q)) 1 (middle.at (.inr T.initial)) := by
    apply Steps.go_at _ n bits middle _ _ (path.index_le P bounded)
    change Instruction.redirect Sum.inl _ (P.instruction n (middle.at q)) = _
    rw [terminal]; rfl
  have mapped' := trace.embeds (P.sequence_right T)
  refine ⟨.inr r,mapped'.prepend (first.trans _ transfer) silent,?_⟩
  change Instruction.redirect Sum.inr .accept (T.instruction n (finish.at r)) = _
  rw [halt]; rfl

end ComplexityOfGenerators.Simulation.WordStack.Program
