import ComplexityOfGenerators.Simulation.AlphabetFallback.Output
import ComplexityOfGenerators.Simulation.AuxiliaryComposition

namespace ComplexityOfGenerators.Simulation.AlphabetFallback

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (bit : α) (allowEmpty : Bool)

theorem fallback_source_no_output (q : CompositionState S (auxiliaryDecision M))
    (index : Option Unit) (origin : Bool) (cell : FallbackSymbol S M)
    (next write work input auxiliary idx emit)
    (table : compositionTransition S (auxiliaryDecision M) q index origin cell =
      .step next write work input auxiliary idx emit) : emit = none := by
  exact auxiliaryComposition_step_no_output S M q index origin cell
    next write work input auxiliary idx emit table

theorem fallback_source_output {n : ℕ} {bits : BitString}
    {c d : CompositionConfiguration S (auxiliaryDecision M)} {t : ℕ}
    (path : (samplerCompositionBank S (auxiliaryDecision M)).Steps (generatorData n) bits c t d) :
    d.output = c.output := by
  exact auxiliaryComposition_output_preserved S M path

theorem fallback_source_exhausted {n : ℕ} {bits : BitString}
    {c : CompositionConfiguration S (auxiliaryDecision M)} {t : ℕ}
    (execution : (samplerCompositionBank S (auxiliaryDecision M)).Executes (generatorData n) bits c t .exhausted) :
    (fallbackBank S M bit allowEmpty).Executes (generatorData n) bits (c.mapState FallbackPhase.source) t .exhausted := by
  obtain ⟨d, no, yes, path, table, absent⟩ := execution.exhausted_path _ rfl
  have target : (fallbackBank S M bit allowEmpty).instruction (generatorData n) (d.mapState FallbackPhase.source) =
      .readRandom (.source no) (.source yes) := by
    change compositionTransition S (auxiliaryDecision M) _ _ _ _ = _ at table
    dsimp only [samplerCompositionBank] at table
    simp only [TransducerBank.TapeBank.instruction, TransducerBank.BankConfiguration.mapState,
      fallbackBank, fallbackSelect, fallbackTransition, table, fallbackSourceInstruction]
  have halt := TransducerBank.TapeBank.Executes.exhausted (d.mapState FallbackPhase.source)
    (.source no) (.source yes) target absent
  simpa using (fallback_source_path S M bit allowEmpty path).executes _ halt

/-- Intercept one final decision, then rewind and emit the selected word. -/
theorem fallback_finish (n : ℕ) (bits : BitString) (word : Word α) (samplerWork : ℤ → Option (Fin S.symbols))
    (samplerHead : ℤ) (c : Configuration (auxiliaryDecision M)) (accepted : Bool)
    (terminal : (auxiliaryDecision M).observe (certificateData n word) bits c =
      .halted (if accepted then .accepted [] else .rejected))
    (emptyOutput : c.output = []) (_headBound : c.auxiliaryHead ≤ word.length) :
    (fallbackBank S M bit allowEmpty).Executes (generatorData n) bits
      ((show CompositionConfiguration S (auxiliaryDecision M) from {recovererBankConfiguration S (auxiliaryDecision M) n word samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}).mapState FallbackPhase.source)
      (c.auxiliaryHead + word.length + 2)
      (.accepted (word.map (fallbackLetter accepted bit))) := by
  let source : CompositionConfiguration S (auxiliaryDecision M) := {recovererBankConfiguration S (auxiliaryDecision M) n word samplerWork samplerHead c with
    state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}
  let start := source.mapState FallbackPhase.source
  let finish : FallbackConfiguration S M := {start with state := .reset accepted}
  have action : (auxiliaryDecision M).transition c.state none word[c.auxiliaryHead]?
      (if c.indexHead < n then some () else none) (c.work c.workHead) =
        if accepted then .accept else .reject := by
    cases accepted <;>
      cases h : (auxiliaryDecision M).transition c.state none word[c.auxiliaryHead]?
        (if c.indexHead < n then some () else none) (c.work c.workHead) <;>
      simp_all [Machine.observe, certificateData]
    all_goals (split_ifs at terminal; cases terminal)
  have enter : (fallbackBank S M bit allowEmpty).Steps (generatorData n) bits start 1 finish := by
    apply TransducerBank.TapeBank.Steps.go _ _ _ _ _ (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
    cases accepted <;>
      simp [TransducerBank.TapeBank.instruction, fallbackBank, fallbackTransition, fallbackSourceInstruction,
        start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
        fallbackSelect, compositionSelect, compositionTransition, action]
  have rest := fallback_reset_emit S M bit allowEmpty n bits word accepted c.auxiliaryHead finish rfl
    (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
    (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
    rfl rfl (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
  simpa [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
    emptyOutput, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using enter.executes _ rest

end
end ComplexityOfGenerators.Simulation.AlphabetFallback
