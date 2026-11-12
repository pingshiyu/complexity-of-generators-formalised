import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native
import ComplexityOfGenerators.Simulation.TransducerBank.Embedding
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

/-! A native bounded-input prefix. A blank work-tape head is a temporary
position counter: scanning and rewinding change no tape symbols. Thus the
original loader starts with its exact blank configuration after both checks. -/

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

open TransducerBank

set_option backward.isDefEq.respectTransparency false

inductive Phase (Q : Type)
  | scan (auxiliary : Bool)
  | rewind (auxiliary : Bool)
  | body (state : Q)
  | drain
  deriving Fintype

variable {I A O Q S : Type} {k : ℕ}

def mapInstruction : BankInstruction Q S O → BankInstruction (Phase Q) S O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (.body no) (.body yes)
  | .step next write work input auxiliary index emit =>
      .step (.body next) write work input auxiliary index emit

variable (B : TapeBank I A O Q S k) (counter : Fin k)

def bank : TapeBank I A O (Phase Q) S k where
  initial := .scan false
  blank := B.blank
  select := fun state => match state with
    | .body state => B.select state
    | _ => counter
  transition := fun state input auxiliary index origin cell => match state with
    | .body state => mapInstruction (B.transition state input auxiliary index origin cell)
    | .drain => .readRandom .drain .drain
    | .scan side =>
        if (if side then auxiliary.isSome else input.isSome) then
          if index.isSome then
            .step (.scan side) cell .right (if side then .stay else .right)
              (if side then .right else .stay) .right none
          else .step .drain cell .stay .stay .stay .stay none
        else .step (.rewind side) cell .stay .stay .stay .stay none
    | .rewind side =>
        if origin then
          .step (if side then .body B.initial else .scan true) cell .stay .stay .stay .stay none
        else .step (.rewind side) cell .left (if side then .stay else .left)
          (if side then .left else .stay) .left none

/-- The temporary counter contains no marks and is reset before handoff. -/
def state (phase : Phase Q) (side : Bool) (position : ℕ) : BankConfiguration O (Phase Q) S k :=
  ⟨phase, if side then 0 else position, if side then position else 0, position,
    0, [], Function.update (fun _ => 0) counter (position : ℤ), fun _ _ => B.blank⟩

def wordLength (data : InputData I A) (side : Bool) : ℕ :=
  if side then data.auxiliary.length else data.input.length

theorem initial_state : state B counter (.scan false) false 0 =
    (bank B counter).initialConfiguration := by
  apply BankConfiguration.ext <;> simp [state, bank, TapeBank.initialConfiguration]

theorem body_instruction (data : InputData I A) (c : BankConfiguration O Q S k) :
    (bank B counter).instruction data (c.mapState Phase.body) =
      mapInstruction (B.instruction data c) := rfl

/-- The checked wrapper changes only the finite control of the body. -/
theorem body_executes (data : InputData I A) (bits : BitString)
    {c : BankConfiguration O Q S k} {ticks : ℕ} {result : Outcome O}
    (run : B.Executes data bits c ticks result) :
    (bank B counter).Executes data bits (c.mapState Phase.body) ticks result := by
  induction run with
  | accept c table => exact .accept _ (by rw [body_instruction, table]; rfl)
  | reject c table => exact .reject _ (by rw [body_instruction, table]; rfl)
  | exhausted c no yes table absent =>
      exact .exhausted _ (.body no) (.body yes) (by rw [body_instruction, table]; rfl) absent
  | random c no yes bit t result table lookup rest ih =>
      apply TapeBank.Executes.random (B := bank B counter) _ (.body no) (.body yes) bit t result
        (by rw [body_instruction, table]; rfl) lookup
      cases bit <;> simpa [TapeBank.choose, BankConfiguration.mapState] using ih
  | step c next write work input auxiliary index emit t result table rest ih =>
      apply TapeBank.Executes.step (B := bank B counter) _ (.body next) write work input auxiliary index emit t result
        (by rw [body_instruction, table]; rfl)
      rw [TapeBank.advance_mapState B (bank B counter) Phase.body (by intro; rfl)]
      exact ih

end ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped
