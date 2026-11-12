import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.Basic
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Embedding

/-! A native bounded-controller event hook. Ordinary controller instructions
execute directly on the fixed alphabet track. An event output is suppressed
and replaced with actual packet preparation, an unbounded original source call,
cleanup, and resumption at the saved finite controller state. Source output is
passed directly to the physical output tape.

The caller proves that event instructions occur at work position zero and
leave the work head there, and that their updated fixed track supplies the
selected unary index. These are concrete call-site invariants, not assumed
source implementations or variance bounds. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

inductive Phase (controllerStates sourceStates sourceSymbols : ℕ) (E O : Type)
  | controller (state : Fin controllerStates)
  | prepare (resume : Fin controllerStates) (event : E) (phase : ParameterInitialisation.Phase)
  | source (resume : Fin controllerStates) (event : E) (phase : NativeSourceCall.Phase O sourceStates sourceSymbols)
  deriving Fintype

variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)

abbrev Fixed := Option (Fin C.symbols)
abbrev Work := Cell (Fixed C) M.symbols

variable (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

def control : Phase C.states M.states M.symbols E O ≃ Fin (Fintype.card (Phase C.states M.states M.symbols E O)) := Fintype.equivFin _

def prepareControl (resume : Fin C.states) (event : E) (state : Fin (Fintype.card ParameterInitialisation.Phase)) :
    Fin (Fintype.card (Phase C.states M.states M.symbols E O)) :=
  control C M (.prepare resume event (ParameterInitialisation.control.symm state))

def sourceControl (resume : Fin C.states) (event : E) (state : Fin (Fintype.card (NativeSourceCall.Phase O M.states M.symbols))) :
    Fin (Fintype.card (Phase C.states M.states M.symbols E O)) :=
  control C M (.source resume event ((NativeSourceCall.control M).symm state))

def transition (phase : Phase C.states M.states M.symbols E O) (input : Option Unit)
    (auxiliary : Option Bool) (index : Option Unit)
    (raw : Option (Fin (Fintype.card (Work C M)))) :
    Instruction O (Fintype.card (Phase C.states M.states M.symbols E O)) (Fintype.card (Work C M)) :=
  let cell := NativeSourceCall.read M raw
  match phase with
  | .controller q =>
      match C.transition q input auxiliary index cell.fixed with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes => .readRandom (control C M (.controller no)) (control C M (.controller yes))
      | .step next write work input auxiliary index emit =>
          .step (control C M (match emit with | none => .controller next | some event => .prepare next event .first))
            (write.map (fun symbol => alphabet M {cell with fixed:=some symbol}))
            work input auxiliary index none
  | .prepare resume event phase =>
      match ParameterInitialisation.transition M (parameter event) phase raw with
      | .accept => .step (control C M (.source resume event (.source (start event)))) none .stay .stay .stay .stay none
      | .reject => .reject
      | .readRandom no yes => .readRandom (prepareControl C M resume event no) (prepareControl C M resume event yes)
      | .step next write work input auxiliary index emit =>
          .step (prepareControl C M resume event next) write work input auxiliary index emit
  | .source resume event phase =>
      match NativeSourceCall.transition M phase raw with
      | .accept => .step (control C M (.controller resume)) none .stay .stay .stay .stay none
      | .reject => .reject
      | .readRandom no yes => .readRandom (sourceControl C M resume event no) (sourceControl C M resume event yes)
      | .step next write work input auxiliary index emit =>
          .step (sourceControl C M resume event next) write work input auxiliary index emit

def routine : Routine Unit Bool O (Fintype.card (Work C M)) where
  states := Fintype.card (Phase C.states M.states M.symbols E O)
  initial := control C M (.controller C.initial)
  transition := fun q input auxiliary index raw => transition C M parameter start ((control C M).symm q) input auxiliary index raw

def machine : Machine Unit Bool O := (routine C M parameter start).machine

@[simp] theorem machine_transition (phase : Phase C.states M.states M.symbols E O) (input auxiliary index raw) :
    (machine C M parameter start).transition (control C M phase) input auxiliary index raw =
      transition C M parameter start phase input auxiliary index raw := by simp [machine,routine,Routine.machine]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
