import ComplexityOfGenerators.Simulation.TranscriptSamplerSteps

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

/-- Exact finite-control simulation of a recorded source execution. Rejected
and exhausted runs retain their outcomes; acceptance returns the transcript. -/
theorem transcriptSampler_of_recording (data : InputData I A) (bits : BitString)
    (c : Configuration M) (log : BitString) (outcome : Outcome O)
    (recorded : M.ExecutionTranscript data bits c log outcome)
    (inputBound : c.inputHead ≤ data.input.length) (auxiliaryBound : c.auxiliaryHead ≤ data.auxiliary.length)
    (indexBound : c.indexHead ≤ data.index) (head : c.workHead ∈ c.visited) (lead : BitString) :
    (transcriptSampler M).runFrom data bits (samplerConfiguration M c lead) (2 * log.length) =
      .halted (samplerOutcome outcome (lead ++ log)) := by
  induction recorded generalizing lead with
  | halt c outcome terminal =>
      simpa only [List.length_nil, Nat.mul_zero, Machine.runFrom, List.append_nil] using
        transcriptSampler_terminal M data bits c lead outcome terminal
  | step c tail outcome state write work input auxiliary index emit action rest ih =>
      have steps := transcriptSampler_step M data bits c lead state write work input auxiliary index emit
        inputBound auxiliaryBound indexBound action
      rw [List.length_cons, show 2 * (tail.length + 1) = 2 + 2 * tail.length by omega,
        (transcriptSampler M).runFrom_add data bits _ _ 2 steps (2 * tail.length)]
      simpa only [List.append_assoc, List.singleton_append] using
        ih (input.onInput_le _ _ inputBound) (auxiliary.onInput_le _ _ auxiliaryBound)
          (index.onInput_le _ _ indexBound) (Finset.mem_insert_self _ _) (lead ++ [false])
  | random c bit tail outcome no yes action lookup rest ih =>
      have steps := transcriptSampler_random M data bits c lead bit no yes
        inputBound auxiliaryBound indexBound head action lookup
      rw [List.length_cons, show 2 * (tail.length + 1) = 2 + 2 * tail.length by omega,
        (transcriptSampler M).runFrom_add data bits _ _ 2 steps (2 * tail.length)]
      simpa only [List.append_assoc, List.singleton_append] using
        ih inputBound auxiliaryBound indexBound head (lead ++ [bit])

/-- Starting from blank tapes adds precisely one padding-output step. -/
theorem transcriptSampler_run_recording (data : InputData I A) (bits : BitString)
    (log : BitString) (outcome : Outcome O)
    (recorded : M.ExecutionTranscript data bits M.initialConfiguration log outcome) :
    (transcriptSampler M).run data bits (2 * log.length + 1) =
      .halted (samplerOutcome outcome (false :: log)) := by
  have boot := transcriptSampler_boot M data bits
  rw [← Machine.runFrom_initial,
    (transcriptSampler M).runFrom_shift data bits _ _ boot.1 boot.2]
  exact transcriptSampler_of_recording M data bits M.initialConfiguration log outcome recorded
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Finset.mem_singleton_self 0) [false]

/-- A bounded source execution supplies a certificate and a bounded sampler
execution on the very same random tape, including both failure outcomes. -/
theorem transcriptSampler_run_halted (data : InputData I A) (bits : BitString)
    (t : ℕ) (outcome : Outcome O) (source : M.run data bits t = .halted outcome) :
    ∃ log, log.length ≤ t ∧ M.ExecutionTranscript data bits M.initialConfiguration log outcome ∧
      (transcriptSampler M).run data bits (2 * t + 1) =
        .halted (samplerOutcome outcome (false :: log)) := by
  obtain ⟨log, length, recorded⟩ := M.executionTranscript_of_runFrom data bits M.initialConfiguration t outcome
    (by simpa only [Machine.runFrom_initial] using source)
  refine ⟨log, length, recorded, ?_⟩
  have halted := transcriptSampler_run_recording M data bits log outcome recorded
  have later := (transcriptSampler M).run_halted_add data bits _ _ halted (2 * (t - log.length))
  have time : 2 * log.length + 1 + 2 * (t - log.length) = 2 * t + 1 := by omega
  simpa only [time] using later

end
end ComplexityOfGenerators.Simulation
