import ComplexityOfGenerators.Simulation.TranscriptSampler

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

theorem transcriptSampler_step (data : InputData I A) (bits : BitString)
    (c : Configuration M) (lead : BitString) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (inputBound : c.inputHead ≤ data.input.length) (auxiliaryBound : c.auxiliaryHead ≤ data.auxiliary.length)
    (indexBound : c.indexHead ≤ data.index)
    (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
      .step state write work input auxiliary index emit) :
    let d := M.stepConfiguration data c state write work input auxiliary index emit
    (transcriptSampler M).runFrom data bits (samplerConfiguration M c lead) 2 =
      (transcriptSampler M).observe data bits (samplerConfiguration M d (lead ++ [false])) := by
  dsimp only
  let d := M.stepConfiguration data c state write work input auxiliary index emit
  have table : (transcriptSampler M).transition (samplerConfiguration M c lead).state
      data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
      .step (samplerControl M (.pad state)) write work input auxiliary index (some false) := by
    simp [transcriptSampler, samplerConfiguration, samplerInstruction, action]
  have live := (transcriptSampler M).observe_step data bits (samplerConfiguration M c lead)
    _ _ _ _ _ _ _ table
  have next : (transcriptSampler M).next data bits (samplerConfiguration M c lead) =
      .running (samplerConfiguration M d (lead ++ [false]) (.pad state)) := by
    rw [(transcriptSampler M).next_step data bits _ _ _ _ _ _ _ _ table]
    cases write <;> cases emit <;> rfl
  have helper := sampler_helper M data bits d (lead ++ [false]) (.pad state) none
    (input.onInput_le _ _ inputBound) (auxiliary.onInput_le _ _ auxiliaryBound)
    (index.onInput_le _ _ indexBound) (Finset.mem_insert_self _ _)
    (by simp [transcriptSampler, d, Machine.stepConfiguration])
  rw [(transcriptSampler M).runFrom_shift data bits _ _ live next 1,
    (transcriptSampler M).runFrom_shift data bits _ _ helper.1 helper.2 0]
  simp only [Option.toList_none, List.append_nil, Machine.runFrom]
  rfl

theorem transcriptSampler_random (data : InputData I A) (bits : BitString)
    (c : Configuration M) (lead : BitString) (bit : Bool) (no yes : Fin M.states)
    (inputBound : c.inputHead ≤ data.input.length) (auxiliaryBound : c.auxiliaryHead ≤ data.auxiliary.length)
    (indexBound : c.indexHead ≤ data.index) (head : c.workHead ∈ c.visited)
    (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) = .readRandom no yes)
    (lookup : bits[c.randomHead]? = some bit) :
    let d := {c with state := if bit then yes else no, randomHead := c.randomHead + 1}
    (transcriptSampler M).runFrom data bits (samplerConfiguration M c lead) 2 =
      (transcriptSampler M).observe data bits (samplerConfiguration M d (lead ++ [bit])) := by
  dsimp only
  let d : Configuration M := {c with state := if bit then yes else no, randomHead := c.randomHead + 1}
  have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have live : (transcriptSampler M).observe data bits (samplerConfiguration M c lead) =
      .running (samplerConfiguration M c lead) := by
    simp [Machine.observe, transcriptSampler, samplerConfiguration, samplerInstruction, action, available]
  have next : (transcriptSampler M).next data bits (samplerConfiguration M c lead) =
      .running (samplerConfiguration M d lead (.emit d.state bit)) := by
    cases bit <;> simp [Machine.next, transcriptSampler, samplerConfiguration, samplerInstruction, action, lookup, d]
  have helper := sampler_helper M data bits d lead (.emit d.state bit) (some bit)
    inputBound auxiliaryBound indexBound head (by simp [transcriptSampler])
  rw [(transcriptSampler M).runFrom_shift data bits _ _ live next 1,
    (transcriptSampler M).runFrom_shift data bits _ _ helper.1 helper.2 0]
  rfl

def samplerOutcome (outcome : Outcome O) (log : BitString) : Outcome Bool :=
  match outcome with
  | .accepted _ => .accepted log
  | .rejected => .rejected
  | .exhausted => .exhausted

theorem transcriptSampler_terminal (data : InputData I A) (bits : BitString)
    (c : Configuration M) (lead : BitString) (outcome : Outcome O)
    (terminal : M.observe data bits c = .halted outcome) :
    (transcriptSampler M).observe data bits (samplerConfiguration M c lead) =
      .halted (samplerOutcome outcome lead) := by
  unfold Machine.observe at terminal
  simp only [Machine.observe, transcriptSampler, samplerConfiguration, Equiv.symm_apply_apply]
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept =>
      simp only [action, RunState.halted.injEq] at terminal
      subst outcome
      rfl
  | reject =>
      simp only [action, RunState.halted.injEq] at terminal
      subst outcome
      rfl
  | step state write work input auxiliary index emit => simp [action] at terminal
  | readRandom no yes =>
      by_cases available : c.randomHead < bits.length
      · simp [action, available] at terminal
      · have same : outcome = .exhausted := by simpa [action, available] using terminal.symm
        subst outcome
        simp [samplerInstruction, available, samplerOutcome]

end
end ComplexityOfGenerators.Simulation
