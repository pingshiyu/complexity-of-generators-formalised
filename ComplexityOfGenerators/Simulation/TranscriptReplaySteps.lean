import ComplexityOfGenerators.Simulation.TranscriptReplay
import ComplexityOfGenerators.Foundations.StepTranscripts

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I O : Type} (M : Machine I Bool O)

def transcriptConfiguration (c : Configuration M) (position : ℕ) : Configuration (transcriptReplay M) where
  state := transcriptControl M (some c.state)
  inputHead := c.inputHead
  auxiliaryHead := position
  indexHead := c.indexHead
  randomHead := 0
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

def transcriptSourceData (input : List I) (n : ℕ) : InputData I Bool := {input := input, index := n}

def transcriptData (input : List I) (n : ℕ) (certificate : BitString) : InputData I Bool :=
  {input := input, auxiliary := certificate, index := n}

theorem transcriptReplay_step (input : List I) (n : ℕ) (lead : BitString) (bit : Bool) (tail bits : BitString)
    (c : Configuration M) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work ordinary auxiliary index : Move) (emit : Option O)
    (action : M.transition c.state input[c.inputHead]? none
      (if c.indexHead < n then some true else none) (c.work c.workHead) =
      .step state write work ordinary auxiliary index emit) :
    let data := transcriptData input n (lead ++ bit :: tail)
    let start := transcriptConfiguration M c lead.length
    let finish := transcriptConfiguration M
      (M.stepConfiguration (transcriptSourceData input n) c state write work ordinary auxiliary index emit)
      (lead.length + 1)
    (transcriptReplay M).observe data bits start = .running start ∧
      (transcriptReplay M).next data bits start = .running finish := by
  dsimp only
  have lookup : (lead ++ bit :: tail)[lead.length]? = some bit := by
    rw [List.getElem?_append_right le_rfl]
    simp
  have table : (transcriptReplay M).transition (transcriptConfiguration M c lead.length).state
      input[c.inputHead]? (some bit) (if c.indexHead < n then some true else none) (c.work c.workHead) =
      .step (transcriptControl M (some state)) write work ordinary .right index emit := by
    simp [transcriptReplay, transcriptConfiguration, transcriptInstruction, action]
  have table' : (transcriptReplay M).transition (transcriptConfiguration M c lead.length).state
      (transcriptData input n (lead ++ bit :: tail)).input[c.inputHead]?
      (transcriptData input n (lead ++ bit :: tail)).auxiliary[lead.length]?
      (if c.indexHead < n then some true else none) (c.work c.workHead) =
      .step (transcriptControl M (some state)) write work ordinary .right index emit := by
    simpa only [transcriptData, lookup] using table
  refine ⟨(transcriptReplay M).observe_step _ bits _ _ _ _ _ _ _ _ table', ?_⟩
  rw [(transcriptReplay M).next_step _ bits _ _ _ _ _ _ _ _ table']
  simp only [Machine.stepConfiguration, transcriptConfiguration, transcriptData, transcriptSourceData,
    Move.onInput, List.length_append, List.length_cons,
    Nat.min_eq_left (show lead.length + 1 ≤ lead.length + (tail.length + 1) by omega)]
  cases write <;> cases emit <;> rfl

theorem transcriptReplay_random (input : List I) (n : ℕ) (lead : BitString) (bit : Bool) (tail bits : BitString)
    (c : Configuration M) (no yes : Fin M.states)
    (inputBound : c.inputHead ≤ input.length) (indexBound : c.indexHead ≤ n)
    (head : c.workHead ∈ c.visited)
    (action : M.transition c.state input[c.inputHead]? none
      (if c.indexHead < n then some true else none) (c.work c.workHead) = .readRandom no yes) :
    let data := transcriptData input n (lead ++ bit :: tail)
    let start := transcriptConfiguration M c lead.length
    let finish := transcriptConfiguration M {c with state := if bit then yes else no, randomHead := 0}
      (lead.length + 1)
    (transcriptReplay M).observe data bits start = .running start ∧
      (transcriptReplay M).next data bits start = .running finish := by
  dsimp only
  have lookup : (lead ++ bit :: tail)[lead.length]? = some bit := by
    rw [List.getElem?_append_right le_rfl]
    simp
  have table : (transcriptReplay M).transition (transcriptConfiguration M c lead.length).state
      input[c.inputHead]? (some bit) (if c.indexHead < n then some true else none) (c.work c.workHead) =
      .step (transcriptControl M (some (if bit then yes else no))) none .stay .stay .right .stay none := by
    simp [transcriptReplay, transcriptConfiguration, transcriptInstruction, action]
  have table' : (transcriptReplay M).transition (transcriptConfiguration M c lead.length).state
      (transcriptData input n (lead ++ bit :: tail)).input[c.inputHead]?
      (transcriptData input n (lead ++ bit :: tail)).auxiliary[lead.length]?
      (if c.indexHead < n then some true else none) (c.work c.workHead) =
      .step (transcriptControl M (some (if bit then yes else no))) none .stay .stay .right .stay none := by
    simpa only [transcriptData, lookup] using table
  refine ⟨(transcriptReplay M).observe_step _ bits _ _ _ _ _ _ _ _ table', ?_⟩
  rw [(transcriptReplay M).next_step _ bits _ _ _ _ _ _ _ _ table']
  simp [Machine.stepConfiguration, transcriptConfiguration, transcriptData,
    Move.onInput, Move.onInt, Nat.min_eq_left inputBound, Nat.min_eq_left indexBound,
    Finset.insert_eq_of_mem head, List.length_append, List.length_cons]

theorem transcriptReplay_boot (input : List I) (n : ℕ) (padding : Bool) (certificate bits : BitString) :
    let data := transcriptData input n (padding :: certificate)
    (transcriptReplay M).observe data bits (transcriptReplay M).initialConfiguration =
        .running (transcriptReplay M).initialConfiguration ∧
      (transcriptReplay M).next data bits (transcriptReplay M).initialConfiguration =
        .running (transcriptConfiguration M M.initialConfiguration 1) := by
  simp [Machine.observe, Machine.next, Machine.initialConfiguration, transcriptReplay,
    transcriptConfiguration, transcriptData, transcriptInstruction, Move.onInput, Move.onInt]

end
end ComplexityOfGenerators.Simulation
