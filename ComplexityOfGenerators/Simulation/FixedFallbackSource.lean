import ComplexityOfGenerators.Simulation.FixedFallbackOutput
import ComplexityOfGenerators.Simulation.AuxiliaryComposition

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (fallback : List α)

theorem fixedFallback_source_exhausted {n : ℕ} {bits : BitString}
    {c : CompositionConfiguration S (auxiliaryDecision M)} {t : ℕ}
    (execution : (samplerCompositionBank S (auxiliaryDecision M)).Executes (generatorData n) bits c t .exhausted) :
    (fixedFallbackBank S M fallback).Executes (generatorData n) bits (c.mapState FixedFallbackPhase.source) t .exhausted := by
  obtain ⟨d, no, yes, path, table, absent⟩ := execution.exhausted_path _ rfl
  have target : (fixedFallbackBank S M fallback).instruction (generatorData n) (d.mapState FixedFallbackPhase.source) =
      .readRandom (.source no) (.source yes) := by
    change compositionTransition S (auxiliaryDecision M) _ _ _ _ = _ at table
    dsimp only [samplerCompositionBank] at table
    simpa only [TransducerBank.TapeBank.instruction, TransducerBank.BankConfiguration.mapState,
      fixedFallbackBank, fixedFallbackSelect, fixedFallbackTransition, table, fixedFallbackSourceInstruction]
  have halt := TransducerBank.TapeBank.Executes.exhausted (d.mapState FixedFallbackPhase.source)
    (.source no) (.source yes) target absent
  simpa using (fixedFallback_source_path S M fallback path).executes _ halt

/-- Intercept one final decision, then rewind and emit the selected word. -/
theorem fixedFallback_finish_accept (n : ℕ) (bits : BitString) (word : List α) (samplerWork : ℤ → Option (Fin S.symbols))
    (samplerHead : ℤ) (c : Configuration (auxiliaryDecision M)) 
    (terminal : (auxiliaryDecision M).observe (certificateData n word) bits c =
      .halted (.accepted []))
    (emptyOutput : c.output = []) (headBound : c.auxiliaryHead ≤ word.length) :
    (fixedFallbackBank S M fallback).Executes (generatorData n) bits
      ((show CompositionConfiguration S (auxiliaryDecision M) from {recovererBankConfiguration S (auxiliaryDecision M) n word samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}).mapState FixedFallbackPhase.source)
      (c.auxiliaryHead + word.length + 2)
      (.accepted (word)) := by
  let source : CompositionConfiguration S (auxiliaryDecision M) := {recovererBankConfiguration S (auxiliaryDecision M) n word samplerWork samplerHead c with
    state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}
  let start : FixedFallbackConfiguration S M fallback := source.mapState FixedFallbackPhase.source
  let finish : FixedFallbackConfiguration S M fallback := {start with state := .reset}
  have action := ((auxiliaryDecision M).accepting_observation terminal).1
  simp only [certificateData, List.getElem?_nil] at action
  have enter : (fixedFallbackBank S M fallback).Steps (generatorData n) bits start 1 finish := by
    apply TransducerBank.TapeBank.Steps.go _ _ _ _ _ (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
    simp [TransducerBank.TapeBank.instruction, fixedFallbackBank, fixedFallbackTransition, fixedFallbackSourceInstruction,
        start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
        fixedFallbackSelect, compositionSelect, compositionTransition, action]
  have rest := fixedFallback_reset_emit S M fallback n bits word c.auxiliaryHead finish rfl
    (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
    (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
    rfl rfl (by simp [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration])
  simpa [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
    emptyOutput, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using enter.executes _ rest


theorem fixedFallback_finish_reject (n : ℕ) (bits : BitString) (word : List α)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ)
    (c : Configuration (auxiliaryDecision M))
    (terminal : (auxiliaryDecision M).observe (certificateData n word) bits c = .halted .rejected)
    (emptyOutput : c.output = []) :
    (fixedFallbackBank S M fallback).Executes (generatorData n) bits
      ((show CompositionConfiguration S (auxiliaryDecision M) from
        {recovererBankConfiguration S (auxiliaryDecision M) n word samplerWork samplerHead c with
          state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}).mapState
            FixedFallbackPhase.source)
      (fallback.length + 1) (.accepted fallback) := by
  let source : CompositionConfiguration S (auxiliaryDecision M) :=
    {recovererBankConfiguration S (auxiliaryDecision M) n word samplerWork samplerHead c with
      state := .recoverWork c.state (decide (c.indexHead < n)) word[c.auxiliaryHead]?}
  let start : FixedFallbackConfiguration S M fallback := source.mapState FixedFallbackPhase.source
  let finish : FixedFallbackConfiguration S M fallback := {start with state := .constant 0}
  have action : (auxiliaryDecision M).transition c.state none word[c.auxiliaryHead]?
      (if c.indexHead < n then some () else none) (c.work c.workHead) = .reject := by
    cases h : (auxiliaryDecision M).transition c.state none word[c.auxiliaryHead]?
        (if c.indexHead < n then some () else none) (c.work c.workHead) <;>
      simp_all [Machine.observe, certificateData]
    split_ifs at terminal <;> cases terminal
  have enter : (fixedFallbackBank S M fallback).Steps (generatorData n) bits start 1 finish := by
    apply TransducerBank.TapeBank.Steps.go _ _ _ _ _
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
      (by simp [start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration, generatorData])
    simp [TransducerBank.TapeBank.instruction, fixedFallbackBank, fixedFallbackTransition,
      fixedFallbackSourceInstruction, start, source, TransducerBank.BankConfiguration.mapState,
      recovererBankConfiguration, fixedFallbackSelect, compositionSelect, compositionTransition, action]
  have rest := fixedFallback_constant S M fallback n bits fallback.length 0 (by simp) finish rfl
  simpa [finish, start, source, TransducerBank.BankConfiguration.mapState, recovererBankConfiguration,
    emptyOutput, Nat.add_comm] using enter.executes _ rest

end
end ComplexityOfGenerators.Simulation
