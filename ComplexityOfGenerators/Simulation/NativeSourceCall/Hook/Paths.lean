import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Basic

/-! Actual primitive paths of packet preparation and source calls embed into
the hooked machine without a compiler or a runtime-dependent simulation loss.
Accepting routine observations remain available for explicit continuation hooks. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

def selectedSource (event : E) : Machine Unit Bool O := {M with initial:=start event}

@[simp] theorem selected_control (event : E) :
    NativeSourceCall.control (selectedSource M start event) = NativeSourceCall.control M := rfl

@[simp] theorem selected_transition (event : E) (phase raw) :
    NativeSourceCall.transition (F:=Fixed C) (selectedSource M start event) phase raw =
      NativeSourceCall.transition M phase raw := by
  cases phase <;> simp only [selectedSource,NativeSourceCall.transition,NativeSourceCall.read,NativeSourceCall.control,NativeSourceCall.alphabet] <;> try rfl
  all_goals repeat' first | simp_all | split

def prepareConfiguration (resume : Fin C.states) (event : E)
    (c : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event))) :
    Configuration (machine C M parameter start) :=
  RoutineEmbedding.configuration (ParameterInitialisation.routine M (parameter event))
    (routine C M parameter start) (prepareControl C M resume event) c

def sourceConfiguration (resume : Fin C.states) (event : E)
    (c : Configuration (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event))) :
    Configuration (machine C M parameter start) :=
  RoutineEmbedding.configuration (NativeSourceCall.routine (selectedSource M start event))
    (routine C M parameter start) (sourceControl C M resume event) c

theorem prepare_table (resume : Fin C.states) (event : E)
    (state : Fin (Fintype.card ParameterInitialisation.Phase)) (input auxiliary index raw)
    (live : RoutineEmbedding.nonterminal (ParameterInitialisation.routine (F:=Fixed C) M (parameter event))
      ((ParameterInitialisation.routine M (parameter event)).transition state input auxiliary index raw)) :
    (routine C M parameter start).transition (prepareControl C M resume event state) input auxiliary index raw =
      RoutineEmbedding.instruction (ParameterInitialisation.routine M (parameter event)) (routine C M parameter start)
        (prepareControl C M resume event) ((ParameterInitialisation.routine M (parameter event)).transition state input auxiliary index raw) := by
  simp only [ParameterInitialisation.routine] at live ⊢
  simp only [routine,prepareControl,Equiv.symm_apply_apply,transition]
  cases action : ParameterInitialisation.transition M (parameter event) (ParameterInitialisation.control.symm state) raw with
  | accept => simp only [RoutineEmbedding.nonterminal,action] at live
  | reject => simp only [RoutineEmbedding.nonterminal,action] at live
  | readRandom no yes => simp [RoutineEmbedding.instruction,prepareControl,sourceControl]
  | step next write work input auxiliary index emit => simp [RoutineEmbedding.instruction,prepareControl,sourceControl]

theorem source_table (resume : Fin C.states) (event : E)
    (state : Fin (Fintype.card (NativeSourceCall.Phase O M.states M.symbols))) (input auxiliary index raw)
    (live : RoutineEmbedding.nonterminal (NativeSourceCall.routine (F:=Fixed C) (selectedSource M start event))
      ((NativeSourceCall.routine (selectedSource M start event)).transition state input auxiliary index raw)) :
    (routine C M parameter start).transition (sourceControl C M resume event state) input auxiliary index raw =
      RoutineEmbedding.instruction (NativeSourceCall.routine (selectedSource M start event)) (routine C M parameter start)
        (sourceControl C M resume event) ((NativeSourceCall.routine (selectedSource M start event)).transition state input auxiliary index raw) := by
  simp only [NativeSourceCall.routine] at live ⊢
  simp only [selected_control,selected_transition] at live ⊢
  simp only [selectedSource] at live ⊢
  simp only [routine,sourceControl,Equiv.symm_apply_apply,transition]
  cases action : NativeSourceCall.transition (F:=Fixed C) M ((NativeSourceCall.control M).symm state) raw with
  | accept => simp only [RoutineEmbedding.nonterminal,action] at live
  | reject => simp only [RoutineEmbedding.nonterminal,action] at live
  | readRandom no yes => simp [RoutineEmbedding.instruction,prepareControl,sourceControl]
  | step next write work input auxiliary index emit => simp [RoutineEmbedding.instruction,prepareControl,sourceControl]

theorem prepare_path (resume : Fin C.states) (event : E) (data : InputData Unit Bool) (bits : BitString)
    {c d : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event))} {ticks : ℕ}
    (path : (ParameterInitialisation.machine M (parameter event)).Steps data bits c ticks d) :
    (machine C M parameter start).Steps data bits
      (prepareConfiguration C M parameter start resume event c) ticks (prepareConfiguration C M parameter start resume event d) :=
  RoutineEmbedding.steps _ _ _ (prepare_table C M parameter start resume event) data bits path

theorem source_path (resume : Fin C.states) (event : E) (data : InputData Unit Bool) (bits : BitString)
    {c d : Configuration (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event))} {ticks : ℕ}
    (path : (NativeSourceCall.machine (selectedSource M start event)).Steps data bits c ticks d) :
    (machine C M parameter start).Steps data bits
      (sourceConfiguration C M parameter start resume event c) ticks (sourceConfiguration C M parameter start resume event d) :=
  RoutineEmbedding.steps _ _ _ (source_table C M parameter start resume event) data bits path

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
