import ComplexityOfGenerators.Simulation.TransducerBank.Execution
import ComplexityOfGenerators.Simulation.OutputMatcher

/-! Streaming output comparison for an arbitrary finite tape bank. It keeps the
source bank's tapes and instruction count; one finite Boolean records a mismatch.
The ordinary target input is the word being compared, while the source's ordinary
input is empty. No output word is materialized on a work tape. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} (B : TapeBank Unit Bool α Q S k)

local instance : DecidableEq α := Classical.decEq α

def instruction (matched : Bool) (input : Option α) :
    BankInstruction Q S α → BankInstruction (Q × Bool) S Unit
  | .accept => if matched && input.isNone then .accept else .reject
  | .reject => .reject
  | .readRandom no yes => .readRandom (no, matched) (yes, matched)
  | .step next write work _ auxiliary index none =>
      .step (next, matched) write work .stay auxiliary index none
  | .step next write work _ auxiliary index (some letter) =>
      .step (next, matched && decide (input = some letter)) write work .right auxiliary index none

def bank : TapeBank α Bool Unit (Q × Bool) S k where
  initial := (B.initial, true)
  blank := B.blank
  select := fun state => B.select state.1
  transition := fun state input auxiliary index origin cell =>
    instruction state.2 input (B.transition state.1 none auxiliary index origin cell)

def sourceData (data : InputData α Bool) : InputData Unit Bool :=
  ⟨[], data.auxiliary, data.index⟩

def configuration (word : Word α) (source : BankConfiguration α Q S k) :
    BankConfiguration Unit (Q × Bool) S k :=
  ⟨(source.state, decide (source.output <+: word)), min source.output.length word.length,
    source.auxiliaryHead, source.indexHead, source.randomHead, [], source.head, source.tape⟩

def outcome (word : Word α) : Outcome α → Outcome Unit
  | .accepted emitted => if emitted = word then .accepted [] else .rejected
  | .rejected => .rejected
  | .exhausted => .exhausted

@[simp] theorem configuration_initial (word : Word α) :
    configuration word B.initialConfiguration = (bank B).initialConfiguration := by
  simp [configuration, TapeBank.initialConfiguration, bank]

theorem configuration_instruction (data : InputData α Bool) (source : BankConfiguration α Q S k) :
    (bank B).instruction data (configuration data.input source) =
      instruction (decide (source.output <+: data.input))
        data.input[min source.output.length data.input.length]?
        (B.instruction (sourceData data) source) := by
  simp [TapeBank.instruction, configuration, bank, sourceData]

theorem configuration_step_none (data : InputData α Bool) (source : BankConfiguration α Q S k)
    (next : Q) (write : S) (work input auxiliary index : Move) :
    (bank B).advance data (configuration data.input source)
      (next, decide (source.output <+: data.input)) write work .stay auxiliary index none =
      configuration data.input
        (B.advance (sourceData data) source next write work input auxiliary index none) := by
  apply BankConfiguration.ext <;>
    simp [TapeBank.advance, configuration, bank, sourceData, Move.onInput,
      Nat.min_assoc]

theorem configuration_step_some (data : InputData α Bool) (source : BankConfiguration α Q S k)
    (next : Q) (write : S) (work input auxiliary index : Move) (letter : α) :
    (bank B).advance data (configuration data.input source)
      (next, decide (source.output <+: data.input) &&
        decide (data.input[min source.output.length data.input.length]? = some letter))
      write work .right auxiliary index none =
      configuration data.input
        (B.advance (sourceData data) source next write work input auxiliary index (some letter)) := by
  have head : min (min source.output.length data.input.length + 1) data.input.length =
      min (source.output ++ [letter]).length data.input.length := by simp; omega
  apply BankConfiguration.ext <;>
    simp [TapeBank.advance, configuration, bank, sourceData, Move.onInput, head,
      matcher_prefix_snoc_bool]

@[simp] theorem configuration_choose (word : Word α) (source : BankConfiguration α Q S k)
    (no yes : Q) (bit : Bool) :
    TapeBank.choose (configuration word source)
      (if bit then (yes, decide (source.output <+: word)) else
        (no, decide (source.output <+: word))) =
      configuration word (TapeBank.choose source (if bit then yes else no)) := by
  cases bit <;> rfl

end
end ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher
