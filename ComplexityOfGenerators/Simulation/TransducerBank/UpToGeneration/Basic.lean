import ComplexityOfGenerators.Simulation.TransducerBank.Execution
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Direct finite-bank up-to generation from a nondeterministic decider

The extra tape first holds a guessed word of length at most the real unary
index. The source decider then reads that immutable tape through finite
lookup/inspect/commit phases. Acceptance rewinds and emits the guessed word;
rejection emits one fixed fallback word. No whole-word operation or source
simulation is a primitive of the transition table. Small indices drain when
shorter than the fixed fallback. The finite sequential symbol chooser covers
every alphabet symbol using boundedly many fair bits; an empty alphabet
always chooses the empty word.
-/

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option synthInstance.maxSize 4096

local instance : Fintype Move := Fintype.ofFinite _

inductive Phase (Q S : Type) (letters fallbackLength tapes : ℕ)
  | shortCheck (position : Fin (fallbackLength + 1))
  | shortRewind (position : Fin (fallbackLength + 1))
  | drain
  | guess
  | symbol (letter : Fin letters)
  | writeLetter (letter : Fin letters)
  | guessRewind
  | fetch (state : Q)
  | inspect (state : Q) (sourceOrigin : Bool) (value : S)
  | commit (selected : Fin tapes) (state : Q) (write : S) (move : Move)
  | acceptRewind
  | emit
  | fallback (position : Fin (fallbackLength + 1))
  deriving Fintype

abbrev Cell (S α : Type) := S × Option α

/-- Clamp the simulated ordinary input to the real guessed-word tape. -/
def inputMove {α : Type} (move : Move) (origin : Bool) (input : Option α) : Move :=
  match move with
  | .left => if origin then .stay else .left
  | .stay => .stay
  | .right => if input.isSome then .right else .stay

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

abbrev Control (_source : TapeBank α Bool Unit Q S k) (word : Word α) :=
  Phase Q S (Fintype.card α) word.length k

def letter (position : Fin (Fintype.card α)) : α := (Fintype.equivFin α).symm position

def bank : TapeBank Unit Bool α (Control B fallback) (Cell S α) (k + 1) where
  initial := .shortCheck 0
  blank := (B.blank, none)
  select := fun phase => match phase with
    | .fetch state => (B.select state).castSucc
    | .commit selected _ _ _ => selected.castSucc
    | _ => Fin.last k
  transition := fun phase _ _ index origin cell => match phase with
    | .shortCheck position =>
      if inside : position.val < fallback.length then
        if index.isSome then
          .step (.shortCheck ⟨position.val + 1, by omega⟩) cell .stay .stay .stay .right none
        else .readRandom .drain .drain
      else .step (.shortRewind position) cell .stay .stay .stay .stay none
    | .shortRewind position =>
      if positive : 0 < position.val then
        .step (.shortRewind ⟨position.val - 1, by omega⟩) cell .stay .stay .stay .left none
      else .step .guess cell .stay .stay .stay .stay none
    | .drain => .readRandom .drain .drain
    | .guess =>
      if alphabetNonempty : 0 < Fintype.card α then
        if index.isSome then .readRandom .guessRewind (.symbol ⟨0, alphabetNonempty⟩)
        else .step .guessRewind cell .stay .stay .stay .stay none
      else .step .guessRewind cell .stay .stay .stay .stay none
    | .symbol position =>
      if more : position.val + 1 < Fintype.card α then
        .readRandom (.writeLetter position) (.symbol ⟨position.val + 1, more⟩)
      else .step (.writeLetter position) cell .stay .stay .stay .stay none
    | .writeLetter position =>
      .step .guess (B.blank, some (letter position)) .right .stay .stay .right none
    | .guessRewind =>
      if origin then .step (.fetch B.initial) cell .stay .stay .stay .stay none
      else .step .guessRewind cell .left .stay .stay .left none
    | .fetch state => .step (.inspect state origin cell.1) cell .stay .stay .stay .stay none
    | .inspect state sourceOrigin value =>
      match B.transition state cell.2 none none sourceOrigin value with
      | .accept => .step .acceptRewind cell .stay .stay .stay .stay none
      | .reject => .step (.fallback 0) cell .stay .stay .stay .stay none
      | .readRandom no yes => .readRandom (.fetch no) (.fetch yes)
      | .step next write work input _ _ _ =>
        .step (.commit (B.select state) next write work) cell
          (inputMove input origin cell.2) .stay .stay .stay none
    | .commit _ state write move =>
      .step (.fetch state) (write, none) move .stay .stay .stay none
    | .acceptRewind =>
      if origin then .step .emit cell .stay .stay .stay .stay none
      else .step .acceptRewind cell .left .stay .stay .stay none
    | .emit =>
      match cell.2 with
      | none => .accept
      | some value => .step .emit cell .right .stay .stay .stay (some value)
    | .fallback position =>
      if inside : position.val < fallback.length then
        .step (.fallback ⟨position.val + 1, by omega⟩) cell .stay .stay .stay .stay
          (some fallback[position.val])
      else .accept

/-- Every explicit rejection from the source is converted to finite fallback
emission. Exhaustion remains the only unsuccessful terminal observation. -/
theorem transition_ne_reject (phase : Control B fallback) (input : Option Unit)
    (auxiliary : Option Bool) (index : Option Unit) (origin : Bool) (cell : Cell S α) :
    (bank B fallback).transition phase input auxiliary index origin cell ≠ .reject := by
  cases phase <;> simp only [bank]
  all_goals first
    | split <;> simp_all
    | intro impossible; cases impossible
  all_goals split <;> simp_all

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
