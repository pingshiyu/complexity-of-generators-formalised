import ComplexityOfGenerators.Simulation.FixedFallbackSource
import ComplexityOfGenerators.Simulation.FixedFallbackGuard
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (fallback : List α)

def fixedFallbackOutcome (word fallback : List α) : Outcome Unit → Outcome α
  | .accepted _ => .accepted word
  | .rejected => .accepted (fallback)
  | .exhausted => .exhausted

/-- Continue an actual sampling path with the decider and output routine. -/
theorem fixedFallback_after_sample (n : ℕ) (bits : BitString) (word : List α) (live : fallback.length ≤ n)
    (c : Configuration S) (samplingTicks : ℕ)
    (path : (samplerCompositionBank S (auxiliaryDecision M)).Steps (generatorData n) bits
      (samplerCompositionBank S (auxiliaryDecision M)).initialConfiguration samplingTicks
      {samplerBankConfiguration S (auxiliaryDecision M) n c with
        state := .sampleWork c.state (decide (c.indexHead < n))})
    (sampled : S.observe (generatorData n) bits c = .halted (.accepted word))
    (indexBound : c.indexHead ≤ n) (randomBound : c.randomHead ≤ bits.length)
    (t : ℕ) (result : Outcome Unit)
    (decision : M.run (decisionData word) (bits.drop c.randomHead) t = .halted result) :
    ∃ ticks, ticks ≤ samplingTicks + n + 3 * word.length + 5 * t + 3 * fallback.length + 12 ∧
      (fixedFallbackBank S M fallback).Executes (generatorData n) bits (fixedFallbackBank S M fallback).initialConfiguration ticks
        (fixedFallbackOutcome word fallback result) := by
  let R := auxiliaryDecision M
  let B := samplerCompositionBank S R
  obtain ⟨action, output⟩ := S.accepting_observation sampled
  have handoff := composition_handoff S R n bits c (by simpa [generatorData] using action)
  rw [output] at handoff
  have recovered : R.run (certificateData n word) (bits.drop c.randomHead) t = .halted (auxiliaryDecisionOutcome result) := by
    rw [auxiliaryDecision_run, decision]; rfl
  have shifted := R.runFrom_drop_random (certificateData n word) bits c.randomHead t randomBound
  rw [recovered] at shifted
  obtain ⟨terminal, recoveryTicks, cost, recoveryPath, halted, finalIndex, finalAuxiliary⟩ :=
    composition_recoverer_runFrom S R n word bits c.work c.workHead
      {R.initialConfiguration with randomHead := c.randomHead} t (auxiliaryDecisionOutcome result) shifted
      (Nat.zero_le _) (Nat.zero_le _)
  have whole := (path.trans B handoff).trans B recoveryPath
  have noOutput : terminal.output = [] := by
    have preserved := auxiliaryComposition_output_preserved S M whole
    simpa only [recovererBankConfiguration, TransducerBank.TapeBank.initialConfiguration] using preserved
  have initial := (fixedFallback_boot S M fallback n bits live).trans _ (fixedFallback_source_path S M fallback whole)
  cases result with
  | accepted out =>
      have finish := fixedFallback_finish_accept S M fallback n bits word c.work c.workHead terminal halted noOutput finalAuxiliary
      have execution := initial.executes _ finish
      refine ⟨_, ?_, by simpa [fixedFallbackOutcome] using execution⟩
      omega
  | rejected =>
      have finish := fixedFallback_finish_reject S M fallback n bits word c.work c.workHead terminal halted noOutput
      have execution := initial.executes _ finish
      refine ⟨_, ?_, by simpa [fixedFallbackOutcome] using execution⟩
      omega
  | exhausted =>
      have finish := composition_recoverer_terminal S R n word bits c.work c.workHead terminal .exhausted halted
      have execution := initial.executes _ (fixedFallback_source_exhausted S M fallback finish)
      refine ⟨_, ?_, by simpa [fixedFallbackOutcome] using execution⟩
      omega


/-- Every finite trial either exhausts or emits the sampled word/fallback. -/
theorem fixedFallback_executes_live (n sampleTime t : ℕ) (bits : BitString) (live : fallback.length ≤ n)
    (sampling : ∀ bits, ∃ result, S.run (generatorData n) bits sampleTime = .halted result ∧
      (match result with | .accepted word => word.length ≤ n | .rejected => False | .exhausted => True))
    (time : ∀ word : List α, word.length ≤ n → M.TimeBound (decisionData word) t) :
    ∃ ticks result, ticks ≤ 10 * n + 5 * sampleTime + 5 * t + 3 * fallback.length + 30 ∧
      (fixedFallbackBank S M fallback).Executes (generatorData n) bits
        (fixedFallbackBank S M fallback).initialConfiguration ticks result ∧
      (match result with
        | .accepted word => (word.length ≤ n ∧ (∃ choices, M.Accepts (decisionData word) choices)) ∨ word = fallback
        | .rejected => False
        | .exhausted => bits.length ≤ 2 * n + 4 * sampleTime + t + 3) := by
  let R := auxiliaryDecision M
  obtain ⟨sampledResult, source, related⟩ := sampling bits
  cases sampledResult with
  | rejected => exact False.elim related
  | exhausted =>
      obtain ⟨terminal, ticks, cost, path, halted, _, _, _⟩ :=
        composition_sampler_prefix S R n bits sampleTime .exhausted source
      obtain ⟨failureTicks, failureCost, failure⟩ := composition_sampler_failure S R n bits terminal .exhausted halted (by intros; simp)
      have initial := (fixedFallback_boot S M fallback n bits live).trans _ (fixedFallback_source_path S M fallback path)
      have short : bits.length ≤ sampleTime := by
        by_contra contrary
        exact S.run_not_exhausted_of_length _ bits sampleTime (by omega) source
      exact ⟨_, .exhausted, by omega,
        initial.executes _ (fixedFallback_source_exhausted S M fallback failure), by omega⟩
  | accepted word =>
      obtain ⟨terminal, ticks, cost, path, halted, indexBound, randomBound, consumed⟩ :=
        composition_sampler_prefix S R n bits sampleTime (.accepted word) source
      obtain ⟨result, decision⟩ := time word related (bits.drop terminal.randomHead)
      obtain ⟨total, totalCost, execution⟩ := fixedFallback_after_sample S M fallback n bits word live terminal ticks path halted
        indexBound randomBound t result decision
      refine ⟨total, fixedFallbackOutcome word fallback result, by omega, execution, ?_⟩
      cases result with
      | accepted out => exact Or.inl ⟨related, ⟨_, out, t, decision⟩⟩
      | rejected => exact Or.inr rfl
      | exhausted =>
          have upper : (bits.drop terminal.randomHead).length ≤ t := by
            by_contra contrary
            exact M.run_not_exhausted_of_length _ _ t (by omega) decision
          simp only [List.length_drop] at upper
          change bits.length ≤ 2 * n + 4 * sampleTime + t + 3
          omega

end
end ComplexityOfGenerators.Simulation
