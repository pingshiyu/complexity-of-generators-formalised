import ComplexityOfGenerators.Simulation.AlphabetFallback.Source
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

namespace ComplexityOfGenerators.Simulation.AlphabetFallback

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (bit : α) (allowEmpty : Bool)

def fallbackOutcome (word : Word α) (bit : α) : Outcome Unit → Outcome α
  | .accepted _ => .accepted word
  | .rejected => .accepted (List.replicate word.length bit)
  | .exhausted => .exhausted

/-- Continue an actual sampling path with the decider and output routine. -/
theorem fallback_after_sample (n : ℕ) (bits : BitString) (word : Word α) (live : n ≠ 0 ∨ allowEmpty = true)
    (c : Configuration S) (samplingTicks : ℕ)
    (path : (samplerCompositionBank S (auxiliaryDecision M)).Steps (generatorData n) bits
      (samplerCompositionBank S (auxiliaryDecision M)).initialConfiguration samplingTicks
      {samplerBankConfiguration S (auxiliaryDecision M) n c with
        state := .sampleWork c.state (decide (c.indexHead < n))})
    (sampled : S.observe (generatorData n) bits c = .halted (.accepted word))
    (indexBound : c.indexHead ≤ n) (randomBound : c.randomHead ≤ bits.length)
    (t : ℕ) (result : Outcome Unit)
    (decision : M.run (decisionData word) (bits.drop c.randomHead) t = .halted result) :
    ∃ ticks, ticks ≤ samplingTicks + n + 3 * word.length + 5 * t + 10 ∧
      (fallbackBank S M bit allowEmpty).Executes (generatorData n) bits (fallbackBank S M bit allowEmpty).initialConfiguration ticks
        (fallbackOutcome word bit result) := by
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
    have preserved := fallback_source_output S M whole
    simpa only [recovererBankConfiguration, TransducerBank.TapeBank.initialConfiguration] using preserved
  have initial := (fallback_boot S M bit allowEmpty n bits live).trans _ (fallback_source_path S M bit allowEmpty whole)
  cases result with
  | accepted out =>
      have finish := fallback_finish S M bit allowEmpty n bits word c.work c.workHead terminal true halted noOutput finalAuxiliary
      have execution := initial.executes _ finish
      refine ⟨_, ?_, by simpa [fallbackOutcome, show fallbackLetter true bit = id from rfl] using execution⟩
      omega
  | rejected =>
      have finish := fallback_finish S M bit allowEmpty n bits word c.work c.workHead terminal false halted noOutput finalAuxiliary
      have execution := initial.executes _ finish
      refine ⟨_, ?_, by simpa [fallbackOutcome, show fallbackLetter false bit = (fun _ => bit) from rfl, List.map_const'] using execution⟩
      omega
  | exhausted =>
      have finish := composition_recoverer_terminal S R n word bits c.work c.workHead terminal .exhausted halted
      have execution := initial.executes _ (fallback_source_exhausted S M bit allowEmpty finish)
      refine ⟨_, ?_, by simpa [fallbackOutcome] using execution⟩
      omega

/-- Size zero is drained when the language does not contain the empty word. -/
theorem fallback_executes_empty (bits : BitString) :
    ∃ ticks, ticks ≤ bits.length + 1 ∧
      (fallbackBank S M bit false).Executes (generatorData 0) bits (fallbackBank S M bit false).initialConfiguration ticks .exhausted := by
  let B := fallbackBank S M bit false
  let c : FallbackConfiguration S M := {B.initialConfiguration with state := .drain}
  have enter : B.Steps (generatorData 0) bits B.initialConfiguration 1 c := by
    apply TransducerBank.TapeBank.Steps.go _ _ _ _ _ (by simp [TransducerBank.TapeBank.initialConfiguration, generatorData])
      (by simp [TransducerBank.TapeBank.initialConfiguration, generatorData])
      (by simp [TransducerBank.TapeBank.initialConfiguration, generatorData])
    rfl
  obtain ⟨ticks, bound, drained⟩ := TransducerBank.TapeBank.drain_executes B (generatorData 0) bits .drain
    (by intros; rfl) bits.length c rfl (by simp [c, TransducerBank.TapeBank.initialConfiguration])
  exact ⟨1 + ticks, by omega, enter.executes B drained⟩

/-- Every finite trial either exhausts or emits the sampled word/fallback. -/
theorem fallback_executes_live (n sampleTime t : ℕ) (bits : BitString) (live : n ≠ 0 ∨ allowEmpty = true)
    (sampling : ∀ bits,∃ result,S.run (generatorData n) bits sampleTime=.halted result ∧
      (match result with | .accepted word=>word.length=n | .rejected=>False | .exhausted=>True))
    (time : ∀ word : Word α,word.length=n → M.TimeBound (decisionData word) t) :
    ∃ ticks result,ticks≤10*n+5*sampleTime+5*t+30 ∧
      (fallbackBank S M bit allowEmpty).Executes (generatorData n) bits
        (fallbackBank S M bit allowEmpty).initialConfiguration ticks result ∧
      (match result with
        | .accepted word=>word.length=n ∧ ((∃ choices,M.Accepts (decisionData word) choices) ∨ word=List.replicate n bit)
        | .rejected=>False
        | .exhausted=>bits.length≤2*n+4*sampleTime+t+3) := by
  let R := auxiliaryDecision M
  obtain ⟨sampledResult,source,related⟩ := sampling bits
  cases sampledResult with
  | rejected => exact False.elim related
  | exhausted =>
      obtain ⟨terminal,ticks,cost,path,halted,_,_,_⟩ :=
        composition_sampler_prefix S R n bits sampleTime .exhausted source
      obtain ⟨failureTicks,failureCost,failure⟩ := composition_sampler_failure S R n bits terminal .exhausted halted (by intros;simp)
      have initial := (fallback_boot S M bit allowEmpty n bits live).trans _ (fallback_source_path S M bit allowEmpty path)
      have short : bits.length≤sampleTime := by
        by_contra contrary
        exact S.run_not_exhausted_of_length _ bits sampleTime (by omega) source
      exact ⟨_,.exhausted,by omega,initial.executes _ (fallback_source_exhausted S M bit allowEmpty failure),by omega⟩
  | accepted word =>
      obtain ⟨terminal,ticks,cost,path,halted,indexBound,randomBound,consumed⟩ :=
        composition_sampler_prefix S R n bits sampleTime (.accepted word) source
      obtain ⟨result,decision⟩ := time word related (bits.drop terminal.randomHead)
      obtain ⟨total,totalCost,execution⟩ := fallback_after_sample S M bit allowEmpty n bits word live terminal ticks path halted
        indexBound randomBound t result decision
      refine ⟨total,fallbackOutcome word bit result,by omega,execution,?_⟩
      cases result with
      | accepted out => exact ⟨related,Or.inl ⟨_,out,t,decision⟩⟩
      | rejected => exact ⟨by simp [related],Or.inr (by simp [related])⟩
      | exhausted =>
          have upper : (bits.drop terminal.randomHead).length≤t := by
            by_contra contrary
            exact M.run_not_exhausted_of_length _ _ t (by omega) decision
          simp only [List.length_drop] at upper
          change bits.length≤2*n+4*sampleTime+t+3
          omega

end
end ComplexityOfGenerators.Simulation.AlphabetFallback
