import ComplexityOfGenerators.Simulation.FallbackSource
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Unit) (bit allowEmpty : Bool)

def fallbackOutcome (word : BitString) (bit : Bool) : Outcome Unit → Outcome Bool
  | .accepted _ => .accepted word
  | .rejected => .accepted (List.replicate word.length bit)
  | .exhausted => .exhausted

/-- Continue an actual sampling path with the decider and output routine. -/
theorem fallback_after_sample (n : ℕ) (bits word : BitString) (live : n ≠ 0 ∨ allowEmpty = true)
    (c : Configuration wordSampler) (samplingTicks : ℕ)
    (path : (samplerCompositionBank wordSampler (auxiliaryDecision M)).Steps (generatorData n) bits
      (samplerCompositionBank wordSampler (auxiliaryDecision M)).initialConfiguration samplingTicks
      {samplerBankConfiguration wordSampler (auxiliaryDecision M) n c with
        state := .sampleWork c.state (decide (c.indexHead < n))})
    (sampled : wordSampler.observe (generatorData n) bits c = .halted (.accepted word))
    (indexBound : c.indexHead ≤ n) (randomBound : c.randomHead ≤ bits.length)
    (t : ℕ) (result : Outcome Unit)
    (decision : M.run (decisionData word) (bits.drop c.randomHead) t = .halted result) :
    ∃ ticks, ticks ≤ samplingTicks + n + 3 * word.length + 5 * t + 10 ∧
      (fallbackBank M bit allowEmpty).Executes (generatorData n) bits (fallbackBank M bit allowEmpty).initialConfiguration ticks
        (fallbackOutcome word bit result) := by
  let R := auxiliaryDecision M
  let B := samplerCompositionBank wordSampler R
  obtain ⟨action, output⟩ := wordSampler.accepting_observation sampled
  have handoff := composition_handoff wordSampler R n bits c (by simpa [generatorData] using action)
  rw [output] at handoff
  have recovered : R.run (generatorData n word) (bits.drop c.randomHead) t = .halted (auxiliaryDecisionOutcome result) := by
    rw [auxiliaryDecision_run, decision]; rfl
  have shifted := R.runFrom_drop_random (generatorData n word) bits c.randomHead t randomBound
  rw [recovered] at shifted
  obtain ⟨terminal, recoveryTicks, cost, recoveryPath, halted, finalIndex, finalAuxiliary⟩ :=
    composition_recoverer_runFrom wordSampler R n word bits c.work c.workHead
      {R.initialConfiguration with randomHead := c.randomHead} t (auxiliaryDecisionOutcome result) shifted
      (Nat.zero_le _) (Nat.zero_le _)
  have whole := (path.trans B handoff).trans B recoveryPath
  have noOutput : terminal.output = [] := by
    have preserved := fallback_source_output M whole
    simpa only [recovererBankConfiguration, TransducerBank.TapeBank.initialConfiguration] using preserved
  have initial := (fallback_boot M bit allowEmpty n bits live).trans _ (fallback_source_path M bit allowEmpty whole)
  cases result with
  | accepted out =>
      have finish := fallback_finish M bit allowEmpty n bits word c.work c.workHead terminal true halted noOutput finalAuxiliary
      have execution := initial.executes _ finish
      refine ⟨_, ?_, by simpa [fallbackOutcome, show fallbackLetter true bit = id from rfl] using execution⟩
      omega
  | rejected =>
      have finish := fallback_finish M bit allowEmpty n bits word c.work c.workHead terminal false halted noOutput finalAuxiliary
      have execution := initial.executes _ finish
      refine ⟨_, ?_, by simpa [fallbackOutcome, show fallbackLetter false bit = (fun _ => bit) from rfl, List.map_const'] using execution⟩
      omega
  | exhausted =>
      have finish := composition_recoverer_terminal wordSampler R n word bits c.work c.workHead terminal .exhausted halted
      have execution := initial.executes _ (fallback_source_exhausted M bit allowEmpty finish)
      refine ⟨_, ?_, by simpa [fallbackOutcome] using execution⟩
      omega

/-- Size zero is drained when the language does not contain the empty word. -/
theorem fallback_executes_empty (bits : BitString) :
    ∃ ticks, ticks ≤ bits.length + 1 ∧
      (fallbackBank M bit false).Executes (generatorData 0) bits (fallbackBank M bit false).initialConfiguration ticks .exhausted := by
  let B := fallbackBank M bit false
  let c : FallbackConfiguration M := {B.initialConfiguration with state := .drain}
  have enter : B.Steps (generatorData 0) bits B.initialConfiguration 1 c := by
    apply TransducerBank.TapeBank.Steps.go _ _ _ _ _ (by simp [TransducerBank.TapeBank.initialConfiguration, generatorData])
      (by simp [TransducerBank.TapeBank.initialConfiguration, generatorData])
      (by simp [TransducerBank.TapeBank.initialConfiguration, generatorData])
    rfl
  obtain ⟨ticks, bound, drained⟩ := TransducerBank.TapeBank.drain_executes B (generatorData 0) bits .drain
    (by intros; rfl) bits.length c rfl (by simp [c, TransducerBank.TapeBank.initialConfiguration])
  exact ⟨1 + ticks, by omega, enter.executes B drained⟩

/-- Every finite trial either exhausts or emits the sampled word/fallback. -/
theorem fallback_executes_live (n t : ℕ) (bits : BitString) (live : n ≠ 0 ∨ allowEmpty = true)
    (time : ∀ word : BitString, word.length = n → M.TimeBound (decisionData word) t) :
    ∃ ticks result, ticks ≤ 20 * n + 5 * t + bits.length + 30 ∧
      (fallbackBank M bit allowEmpty).Executes (generatorData n) bits (fallbackBank M bit allowEmpty).initialConfiguration ticks result ∧
      (match result with
        | .accepted word => word.length = n ∧ ((∃ choices, M.Accepts (decisionData word) choices) ∨ word = List.replicate n bit)
        | .rejected => False
        | .exhausted => bits.length ≤ 10 * n + t + 3) := by
  let R := auxiliaryDecision M
  by_cases short : bits.length < n
  · have source : wordSampler.run (generatorData n) bits (2 * n) = .halted .exhausted := by
      simpa [wordSamplerOutcome, short] using wordSampler_run n bits
    obtain ⟨terminal, ticks, cost, path, halted, _, _, _⟩ := composition_sampler_prefix wordSampler R n bits (2 * n) .exhausted source
    obtain ⟨failureTicks, failureCost, failure⟩ := composition_sampler_failure wordSampler R n bits terminal .exhausted halted (by intros; simp)
    have initial := (fallback_boot M bit allowEmpty n bits live).trans _ (fallback_source_path M bit allowEmpty path)
    exact ⟨_, .exhausted, by omega, initial.executes _ (fallback_source_exhausted M bit allowEmpty failure), by omega⟩
  · let word := bits.take n
    have length : word.length = n := by simp [word, List.length_take, Nat.min_eq_left (by omega : n ≤ bits.length)]
    have source : wordSampler.run (generatorData n) bits (2 * n) = .halted (.accepted word) := by
      simpa [wordSamplerOutcome, short, word] using wordSampler_run n bits
    obtain ⟨terminal, ticks, cost, path, halted, indexBound, randomBound, consumed⟩ :=
      composition_sampler_prefix wordSampler R n bits (2 * n) (.accepted word) source
    obtain ⟨result, decision⟩ := time word length (bits.drop terminal.randomHead)
    obtain ⟨total, totalCost, execution⟩ := fallback_after_sample M bit allowEmpty n bits word live terminal ticks path halted indexBound randomBound t result decision
    refine ⟨total, fallbackOutcome word bit result, by omega, execution, ?_⟩
    cases result with
    | accepted out => exact ⟨length, Or.inl ⟨_, out, t, decision⟩⟩
    | rejected => exact ⟨by simp [fallbackOutcome, length], Or.inr (by simp [fallbackOutcome, length])⟩
    | exhausted =>
        have upper : (bits.drop terminal.randomHead).length ≤ t := by
          by_contra contrary
          exact M.run_not_exhausted_of_length _ _ t (by omega) decision
        simp only [List.length_drop] at upper
        change bits.length ≤ 10 * n + t + 3
        omega

end
end ComplexityOfGenerators.Simulation
