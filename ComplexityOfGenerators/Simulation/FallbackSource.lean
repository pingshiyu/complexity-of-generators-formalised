import ComplexityOfGenerators.Simulation.FallbackOutput
import ComplexityOfGenerators.Simulation.CompositionExecution

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Unit) (bit allowEmpty : Bool)

theorem fallback_source_no_output (q : CompositionState wordSampler (auxiliaryDecision M))
    (index : Option Unit) (origin : Bool) (cell : FallbackSymbol M)
    (next write work input auxiliary idx emit)
    (table : compositionTransition wordSampler (auxiliaryDecision M) q index origin cell =
      .step next write work input auxiliary idx emit) : emit = none := by
  cases q
  case recoverWork q idx certificate =>
    cases action : M.transition q certificate none none cell.recoverer <;>
      simp only [compositionTransition, auxiliaryDecision, action] at table
    all_goals repeat' split at table
    all_goals simp_all
  all_goals simp only [compositionTransition] at table
  all_goals repeat' split at table
  all_goals simp_all

theorem fallback_source_output {n : ℕ} {bits : BitString}
    {c d : CompositionConfiguration wordSampler (auxiliaryDecision M)} {t : ℕ}
    (path : (samplerCompositionBank wordSampler (auxiliaryDecision M)).Steps (generatorData n) bits c t d) :
    d.output = c.output := by
  induction path with
  | refl => rfl
  | random c no yes letter t d table lookup rest ih => exact ih
  | step c next write work input auxiliary index emit t d table rest ih =>
      have absent := fallback_source_no_output M _ _ _ _ _ _ _ _ _ _ _ table
      simpa [TransducerBank.TapeBank.advance, absent] using ih

theorem fallback_source_exhausted {n : ℕ} {bits : BitString}
    {c : CompositionConfiguration wordSampler (auxiliaryDecision M)} {t : ℕ}
    (execution : (samplerCompositionBank wordSampler (auxiliaryDecision M)).Executes (generatorData n) bits c t .exhausted) :
    (fallbackBank M bit allowEmpty).Executes (generatorData n) bits (c.mapState FallbackPhase.source) t .exhausted := by
  obtain ⟨d, no, yes, path, table, absent⟩ := execution.exhausted_path _ rfl
  have target : (fallbackBank M bit allowEmpty).instruction (generatorData n) (d.mapState FallbackPhase.source) =
      .readRandom (.source no) (.source yes) := by
    change compositionTransition wordSampler (auxiliaryDecision M) _ _ _ _ = _ at table
    dsimp only [samplerCompositionBank] at table
    simpa only [TransducerBank.TapeBank.instruction, TransducerBank.BankConfiguration.mapState,
      fallbackBank, fallbackSelect, fallbackTransition, table, fallbackSourceInstruction]
  have halt := TransducerBank.TapeBank.Executes.exhausted (d.mapState FallbackPhase.source)
    (.source no) (.source yes) target absent
  simpa using (fallback_source_path M bit allowEmpty path).executes _ halt

/-- Intercept one final decision, then rewind and emit the selected word. -/
theorem fallback_finish (n : ℕ) (bits word : BitString) (samplerWork : ℤ → Option (Fin wordSampler.symbols))
    (samplerHead : ℤ) (c : Configuration (auxiliaryDecision M)) (accepted : Bool)
    (terminal : (auxiliaryDecision M).observe (generatorData n word) bits c =
      .halted (if accepted then .accepted [] else .rejected))
    (emptyOutput : c.output = []) (headBound : c.auxiliaryHead ≤ word.length) :
    (fallbackBank M bit allowEmpty).Executes (generatorData n) bits
      ((show CompositionConfiguration wordSampler (auxiliaryDecision M) from {recovererBankConfiguration wordSampler (auxiliaryDecision M) n word samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}).mapState FallbackPhase.source)
      (c.auxiliaryHead + word.length + 2)
      (.accepted (word.map (fallbackLetter accepted bit))) := by
  let source : CompositionConfiguration wordSampler (auxiliaryDecision M) := {recovererBankConfiguration wordSampler (auxiliaryDecision M) n word samplerWork samplerHead c with
    state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}
  let start := source.mapState FallbackPhase.source
  let finish : FallbackConfiguration M := {start with state := .reset accepted}
  have action : (auxiliaryDecision M).transition c.state none word[c.auxiliaryHead]?
      (if c.indexHead < n then some () else none) (c.work c.workHead) =
        if accepted then .accept else .reject := by
    cases accepted <;>
      cases h : (auxiliaryDecision M).transition c.state none word[c.auxiliaryHead]?
        (if c.indexHead < n then some () else none) (c.work c.workHead) <;>
      simp_all [Machine.observe, generatorData]
    all_goals split_ifs at terminal <;> cases terminal
  have enter : (fallbackBank M bit allowEmpty).Steps (generatorData n) bits start 1 finish := by
    apply TransducerBank.TapeBank.Steps.go _ _ _ _ _ (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
    cases accepted <;>
      simp [TransducerBank.TapeBank.instruction, fallbackBank, fallbackTransition, fallbackSourceInstruction,
        start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
        fallbackSelect, compositionSelect, compositionTransition, action]
  have rest := fallback_reset_emit M bit allowEmpty n bits word accepted c.auxiliaryHead finish rfl
    (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
    (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
    rfl rfl (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
  simpa [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
    emptyOutput, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using enter.executes _ rest

end
end ComplexityOfGenerators.Simulation
