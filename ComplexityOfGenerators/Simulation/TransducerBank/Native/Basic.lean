import ComplexityOfGenerators.MultitapeModel
import ComplexityOfGenerators.Foundations.ExecutionTranscripts

/-! The native finite machine is a one-tape bank without simulation overhead.
The bank explicitly writes the currently observed cell when the native program
chooses `none`; this makes every individual transition agree. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.Native

variable {I A O : Type} (M : Machine I A O)

def bank : TapeBank I A O (Fin M.states) (Option (Fin M.symbols)) 1 where
  initial := M.initial
  blank := none
  select := fun _ => 0
  transition := fun state input auxiliary index _ cell =>
    match M.transition state input auxiliary index cell with
    | .accept => .accept
    | .reject => .reject
    | .readRandom no yes => .readRandom no yes
    | .step next write work input auxiliary index emit =>
        .step next (write.or cell) work input auxiliary index emit

def machine : MultitapeMachine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  Control := Fin M.states
  Work := Option (Fin M.symbols)
  controlFinite := inferInstance
  workFinite := inferInstance
  tapes := 1
  program := bank M

def configuration (source : Configuration M) :
    BankConfiguration O (Fin M.states) (Option (Fin M.symbols)) 1 :=
  ⟨source.state, source.inputHead, source.auxiliaryHead, source.indexHead,
    source.randomHead, source.output, fun _ => source.workHead, fun _ => source.work⟩

@[simp] theorem configuration_initial :
    configuration M M.initialConfiguration = (bank M).initialConfiguration := rfl

@[simp] theorem configuration_random (source : Configuration M) (next : Fin M.states) :
    configuration M {source with state := next, randomHead := source.randomHead + 1} =
      TapeBank.choose (configuration M source) next := rfl

@[simp] theorem configuration_step (data : InputData I A) (source : Configuration M)
    (next : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O) :
    configuration M (M.stepConfiguration data source next write work input auxiliary index emit) =
      (bank M).advance data (configuration M source) next (write.or (source.work source.workHead))
        work input auxiliary index emit := by
  have unique : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim j 0
  cases emit <;> cases write <;> ext : 1 <;>
    simp [configuration, Machine.stepConfiguration, TapeBank.advance,
      bank, funext_iff, unique, Function.update_eq_self]

end ComplexityOfGenerators.Simulation.TransducerBank.Native
