import ComplexityOfGenerators.Simulation.CompositionHandoff
import ComplexityOfGenerators.Foundations.RandomTapeShift
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

theorem runFrom_drop_random (data : InputData I A) (bits : BitString) (position t : ℕ)
    (bound : position ≤ bits.length) :
    M.runFrom data bits {M.initialConfiguration with randomHead := position} t =
      M.shiftRandomResult (bits.take position) (M.run data (bits.drop position) t) := by
  have shifted := M.runFrom_shift_random data (bits.take position) (bits.drop position) M.initialConfiguration t
  rw [runFrom_initial] at shifted
  simpa [List.take_append_drop, shiftRandomConfiguration, initialConfiguration,
    List.length_take, Nat.min_eq_left bound, runFrom_initial] using shifted

theorem accepting_observation {data : InputData I A} {bits : BitString} {c : Configuration M} {word : List O}
    (accepted : M.observe data bits c = .halted (.accepted word)) :
    M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) = .accept ∧ c.output = word := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => exact ⟨rfl, by simpa [observe, action] using accepted⟩
  | reject => simp [observe, action] at accepted
  | step state write work input auxiliary index emit => simp [observe, action] at accepted
  | readRandom no yes =>
      simp only [observe, action] at accepted
      split_ifs at accepted
      cases accepted

end ComplexityOfGenerators.Machine

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

/-- Start from blank tapes, load the parameter, and reach the first terminal
sampler observation. The returned random cursor is within the supplied tape. -/
theorem composition_sampler_prefix (n : ℕ) (bits : BitString) (t : ℕ) (result : Outcome Bool)
    (source : S.run (generatorData n) bits t = .halted result) :
    ∃ terminal ticks, ticks ≤ 2 * n + 4 * t + 3 ∧
      (samplerCompositionBank S R).Steps (generatorData n) bits (samplerCompositionBank S R).initialConfiguration ticks
        {samplerBankConfiguration S R n terminal with
          state := .sampleWork terminal.state (decide (terminal.indexHead < n))} ∧
      S.observe (generatorData n) bits terminal = .halted result ∧ terminal.indexHead ≤ n ∧
      terminal.randomHead ≤ bits.length ∧ terminal.randomHead ≤ ticks := by
  obtain ⟨terminal, ticks, cost, path, halted, indexBound⟩ := composition_sampler_runFrom S R n bits S.initialConfiguration
    t result (by simpa only [Machine.runFrom_initial] using source) (Nat.zero_le _)
  have loaded := composition_loaded S R n bits
  have allSteps := loaded.trans _ path
  refine ⟨terminal, 2 * n + 2 + ticks, by omega, allSteps, halted, indexBound, ?_, ?_⟩
  · exact allSteps.random_le_length _ (Nat.zero_le _)
  · simpa [TransducerBank.TapeBank.initialConfiguration, samplerBankConfiguration] using allSteps.random_growth _

/-- Explicit sampler rejection is implemented by consuming the remaining
random tape, including when that tape is already exhausted. -/
theorem composition_sampler_failure (n : ℕ) (bits : BitString) (c : Configuration S)
    (result : Outcome Bool) (terminal : S.observe (generatorData n) bits c = .halted result)
    (failed : ∀ certificate, result ≠ .accepted certificate) :
    ∃ ticks, ticks ≤ bits.length + 1 ∧ (samplerCompositionBank S R).Executes (generatorData n) bits
      {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))} ticks .exhausted := by
  let B := samplerCompositionBank S R
  let start : CompositionConfiguration S R :=
    {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))}
  cases action : S.transition c.state none none (if c.indexHead < n then some () else none) (c.work c.workHead) with
  | accept =>
      have equal : result = .accepted c.output := by simpa [Machine.observe, generatorData, action] using terminal.symm
      exact False.elim (failed c.output equal)
  | step state write work input auxiliary index emit => simp [Machine.observe, generatorData, action] at terminal
  | reject =>
      have table : B.instruction (generatorData n) start = .readRandom .drain .drain := by
        simp [B, start, TransducerBank.TapeBank.instruction, samplerCompositionBank, samplerBankConfiguration,
          compositionSelect, compositionTransition, action]
      cases lookup : bits[c.randomHead]? with
      | none => exact ⟨0, Nat.zero_le _, .exhausted _ _ _ table lookup⟩
      | some bit =>
          obtain ⟨ticks, cost, rest⟩ := TransducerBank.TapeBank.drain_executes B (generatorData n) bits .drain
            (by intros; rfl) bits.length (TransducerBank.TapeBank.choose start .drain) rfl (by simp [TransducerBank.TapeBank.choose])
          refine ⟨ticks + 1, by omega, .random start .drain .drain bit ticks .exhausted table lookup ?_⟩
          simpa using rest
  | readRandom no yes =>
      have unavailable : ¬c.randomHead < bits.length := by
        by_contra available
        simp [Machine.observe, generatorData, action, available] at terminal
      refine ⟨0, Nat.zero_le _, .exhausted _ (.sample no) (.sample yes) ?_ ?_⟩
      · simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, samplerBankConfiguration,
          compositionSelect, compositionTransition, action]
      · exact List.getElem?_eq_none (by change bits.length ≤ c.randomHead; omega)

end
end ComplexityOfGenerators.Simulation
