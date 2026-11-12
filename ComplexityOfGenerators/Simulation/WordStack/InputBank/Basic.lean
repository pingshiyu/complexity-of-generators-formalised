import ComplexityOfGenerators.Simulation.WordStack.Compiler

/-!
Ordinary-word input for finite word-stack controllers. A native tape-bank
prefix loads both read-only words into designated stacks before entering the
existing controller. Each letter is loaded by two primitive bank steps.
-/

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank

open TransducerBank

set_option backward.isDefEq.respectTransparency false

inductive Phase (I A Q S : Type) (k : ℕ)
  | input
  | inputWrite (letter : I)
  | auxiliary
  | auxiliaryWrite (letter : A)
  | body (state : WordStack.Phase Q S k)
  deriving Fintype

def mapInstruction {I A Q S O : Type} {k : ℕ} :
    BankInstruction (WordStack.Phase Q S k) (Option S) O →
      BankInstruction (Phase I A Q S k) (Option S) O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (.body no) (.body yes)
  | .step next write work input auxiliary index emit =>
      .step (.body next) write work input auxiliary index emit

variable {I A Q S O : Type} {k : ℕ} (P : Program Q S O k)
    (inputStack auxiliaryStack : Fin k) (encodeInput : I → S) (encodeAuxiliary : A → S)

def bank : TapeBank I A O (Phase I A Q S k) (Option S) k where
  initial := .input
  blank := none
  select := fun state => match state with
    | .input | .inputWrite _ => inputStack
    | .auxiliary | .auxiliaryWrite _ => auxiliaryStack
    | .body state => P.bankSelect state
  transition := fun state input auxiliary index origin cell => match state with
    | .input => match input with
      | none => .step .auxiliary cell .stay .stay .stay .stay none
      | some letter => .step (.inputWrite letter) cell .right .right .stay .stay none
    | .inputWrite letter => .step .input (some (encodeInput letter)) .stay .stay .stay .stay none
    | .auxiliary => match auxiliary with
      | none => .step (.body (.ready P.initial)) cell .stay .stay .stay .stay none
      | some letter => .step (.auxiliaryWrite letter) cell .right .stay .right .stay none
    | .auxiliaryWrite letter => .step .auxiliary (some (encodeAuxiliary letter)) .stay .stay .stay .stay none
    | .body state => mapInstruction (P.bankTransition state index origin cell)

/-- Read-only heads stay at the ends reached by the loading prefix. -/
def externalize (data : InputData I A)
    (c : BankConfiguration O (WordStack.Phase Q S k) (Option S) k) :
    BankConfiguration O (Phase I A Q S k) (Option S) k :=
  ⟨.body c.state, data.input.length, data.auxiliary.length, c.indexHead, c.randomHead,
    c.output, c.head, c.tape⟩

theorem external_instruction (data : InputData I A)
    (c : BankConfiguration O (WordStack.Phase Q S k) (Option S) k) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).instruction data (externalize data c) =
      mapInstruction (P.bank.instruction (generatorData data.index) c) := rfl

theorem external_choose (data : InputData I A)
    (c : BankConfiguration O (WordStack.Phase Q S k) (Option S) k) (next : WordStack.Phase Q S k) :
    TapeBank.choose (externalize data c) (.body next) = externalize data (TapeBank.choose c next) := rfl

theorem external_moves (phase : WordStack.Phase Q S k) (index : Option Unit) (origin : Bool) (cell : Option S)
    (next write work input auxiliary move emit)
    (table : P.bankTransition phase index origin cell = .step next write work input auxiliary move emit) :
    input = .stay ∧ auxiliary = .stay := by
  cases phase with
  | push next stack symbol => cases table; exact ⟨rfl, rfl⟩
  | ready state =>
    cases command : P.transition state cell index with
    | accept => simp [Program.bankTransition, command] at table
    | reject => simp [Program.bankTransition, command] at table
    | random no yes => simp [Program.bankTransition, command] at table
    | step target action move emit =>
      cases action <;> simp only [Program.bankTransition, command] at table <;>
        cases table <;> exact ⟨rfl, rfl⟩

theorem external_advance (data : InputData I A)
    (c : BankConfiguration O (WordStack.Phase Q S k) (Option S) k)
    (next write work move emit) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).advance data (externalize data c)
      (.body next) write work .stay .stay move emit =
      externalize data (P.bank.advance (generatorData data.index) c next write work .stay .stay move emit) := by
  apply BankConfiguration.ext <;>
    simp [bank, Program.bank, generatorData, externalize, TapeBank.advance, Move.onInput]

/-- Existing finite stack execution proofs remain valid after ordinary words
are loaded. The adapter changes neither the controller's steps nor its coins. -/
theorem external_executes (data : InputData I A) (bits : BitString)
    {c : BankConfiguration O (WordStack.Phase Q S k) (Option S) k} {ticks : ℕ} {result : Outcome O}
    (execution : P.bank.Executes (generatorData data.index) bits c ticks result) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Executes data bits
      (externalize data c) ticks result := by
  induction execution with
  | accept c table => exact .accept _ (by rw [external_instruction, table]; rfl)
  | reject c table => exact .reject _ (by rw [external_instruction, table]; rfl)
  | exhausted c no yes table absent =>
    exact .exhausted _ (.body no) (.body yes) (by rw [external_instruction, table]; rfl) absent
  | random c no yes bit t result table lookup rest ih =>
    apply TapeBank.Executes.random (B := bank P inputStack auxiliaryStack encodeInput encodeAuxiliary)
      _ (Phase.body no) (Phase.body yes) bit t result
      (by rw [external_instruction, table]; rfl) lookup
    cases bit <;> simpa [external_choose] using ih
  | step c next write work input auxiliary move emit t result table rest ih =>
    have moves := external_moves P c.state (if c.indexHead < data.index then some () else none)
      (decide (c.head (P.bankSelect c.state) = 0))
      (c.tape (P.bankSelect c.state) (c.head (P.bankSelect c.state)))
      next write work input auxiliary move emit table
    obtain ⟨rfl, rfl⟩ := moves
    apply TapeBank.Executes.step (B := bank P inputStack auxiliaryStack encodeInput encodeAuxiliary)
      _ (Phase.body next) write work .stay .stay move emit t result
      (by rw [external_instruction, table]; rfl)
    simpa only [external_advance] using ih

end ComplexityOfGenerators.Simulation.WordStack.InputBank
