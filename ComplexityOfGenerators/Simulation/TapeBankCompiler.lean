import ComplexityOfGenerators.Simulation.TapeBank
import ComplexityOfGenerators.Simulation.TransducerBank.Compiler

/-! Decision banks use the general transducer compiler. The translation keeps
one instruction per source instruction, emits nothing, and never reads random
bits. The collision-checker interface remains decision-only. -/

namespace ComplexityOfGenerators.Simulation

set_option backward.isDefEq.respectTransparency false

variable {Q S : Type} {k : ℕ}

def BankInstruction.toTransducer : BankInstruction Q S → TransducerBank.BankInstruction Q S Unit
  | .accept => .accept
  | .reject => .reject
  | .step next write work input => .step next write work input .stay .stay none

def TapeBank.toTransducer (B : TapeBank Q S k) : TransducerBank.TapeBank Bool Bool Unit Q S k where
  initial := B.initial
  blank := B.blank
  select := B.select
  transition := fun q input _ _ origin symbol => (B.transition q input origin symbol).toTransducer

def BankConfiguration.toTransducer (c : BankConfiguration Q S k) :
    TransducerBank.BankConfiguration Unit Q S k :=
  ⟨c.state, c.inputHead, 0, 0, 0, [], c.head, c.tape⟩

def bankOutcome (accepted : Bool) : Outcome Unit :=
  if accepted then .accepted [] else .rejected

namespace TapeBank

variable (B : TapeBank Q S k)

@[simp] theorem toTransducer_initial :
    B.toTransducer.initialConfiguration = B.initialConfiguration.toTransducer := rfl

@[simp] theorem toTransducer_instruction (word : BitString) (c : BankConfiguration Q S k) :
    B.toTransducer.instruction (decisionData word) c.toTransducer =
      (B.instruction word c).toTransducer := rfl

@[simp] theorem toTransducer_advance (word : BitString) (c : BankConfiguration Q S k)
    (next write work input) :
    B.toTransducer.advance (decisionData word) c.toTransducer next write work input .stay .stay none =
      (B.advance word c next write work input).toTransducer := by
  simp [toTransducer, BankConfiguration.toTransducer, TransducerBank.TapeBank.advance,
    advance, decisionData, Move.onInput]

theorem Executes.toTransducer {word : BitString} {c : BankConfiguration Q S k} {t result}
    (exec : B.Executes word c t result) (bits : BitString) :
    B.toTransducer.Executes (decisionData word) bits c.toTransducer t (bankOutcome result) := by
  induction exec with
  | accept c table =>
      exact .accept _ (by simp [table, BankInstruction.toTransducer])
  | reject c table =>
      exact .reject _ (by simp [table, BankInstruction.toTransducer])
  | step c next write work input t result table rest ih =>
      apply TransducerBank.TapeBank.Executes.step _ next write work input .stay .stay none t _
        (by simp [table, BankInstruction.toTransducer])
      simpa using ih

theorem toTransducer_deterministic : B.toTransducer.Deterministic := by
  intro q input auxiliary index origin symbol
  dsimp only [toTransducer]
  cases B.transition q input origin symbol <;> trivial

end TapeBank

noncomputable section

variable [Fintype Q] [Fintype S] (B : TapeBank Q S k)

def bankMachine : Machine Bool Bool Unit := TransducerBank.bankMachine B.toTransducer

theorem bankMachine_deterministic : (bankMachine B).Deterministic :=
  TransducerBank.bankMachine_deterministic B.toTransducer B.toTransducer_deterministic

end
end ComplexityOfGenerators.Simulation
