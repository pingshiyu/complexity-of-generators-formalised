import ComplexityOfGenerators.Simulation.CompositionLoader
import ComplexityOfGenerators.Simulation.CompositionSamplerRun
import ComplexityOfGenerators.Simulation.CompositionRecovererRun
import ComplexityOfGenerators.Simulation.TransducerBank.RandomTape

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

/-- Acceptance by the sampler rewinds the virtual index and the complete
certificate, then enters the recoverer on its untouched blank work tape. -/
theorem composition_handoff (n : ℕ) (bits : BitString) (c : Configuration S)
    (action : S.transition c.state none none (if c.indexHead < n then some () else none) (c.work c.workHead) = .accept) :
    (samplerCompositionBank S R).Steps (generatorData n) bits
      {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))}
      (c.indexHead + c.output.length + 3)
      (recovererBankConfiguration S R n c.output c.work c.workHead
        {R.initialConfiguration with randomHead := c.randomHead}) := by
  let B := samplerCompositionBank S R
  let start : CompositionConfiguration S R :=
    {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))}
  let resetIndex : CompositionConfiguration S R := {start with state := .resetIndex}
  let resetCertificate : CompositionConfiguration S R :=
    {resetIndex with state := .resetCertificate, head := Function.update resetIndex.head 1 0}
  have enter : B.Steps (generatorData n) bits start 1 resetIndex := by
    apply TransducerBank.TapeBank.Steps.go <;>
      simp [B, start, samplerBankConfiguration, generatorData, TransducerBank.TapeBank.instruction,
        samplerCompositionBank, compositionSelect, compositionTransition, action]
  have indexReset := TransducerBank.TapeBank.rewind_steps B (generatorData n) bits .resetIndex .resetCertificate 1
    rfl (by intro input auxiliary index origin cell; cases origin <;> rfl) c.indexHead resetIndex rfl
    (by simp [resetIndex, start, samplerBankConfiguration]) (Nat.zero_le _) (Nat.zero_le _) le_rfl
  have certificateReset := TransducerBank.TapeBank.rewind_steps B (generatorData n) bits .resetCertificate (.recover R.initial) 2
    rfl (by intro input auxiliary index origin cell; cases origin <;> rfl) c.output.length resetCertificate rfl
    (by simp [resetCertificate, resetIndex, start, samplerBankConfiguration]) (Nat.zero_le _) (Nat.zero_le _) le_rfl
  have finished : {resetCertificate with
      state := .recover R.initial
      head := Function.update resetCertificate.head 2 0} =
      recovererBankConfiguration S R n c.output c.work c.workHead
        {R.initialConfiguration with randomHead := c.randomHead} := by
    apply TransducerBank.BankConfiguration.ext
    all_goals try rfl
    · funext j
      fin_cases j <;> simp [resetCertificate, resetIndex, start, samplerBankConfiguration,
        recovererBankConfiguration, Machine.initialConfiguration]
  rw [finished] at certificateReset
  convert (enter.trans B indexReset).trans B certificateReset using 1 <;> omega

/-- At the final recoverer observation, native acceptance, rejection or actual
random exhaustion is returned without any extra machine instruction. -/
theorem composition_recoverer_terminal (n : ℕ) (certificate bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (c : Configuration R)
    (result : Outcome α) (terminal : R.observe (generatorData n certificate) bits c = .halted result) :
    (samplerCompositionBank S R).Executes (generatorData n) bits
      {recovererBankConfiguration S R n certificate samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) certificate[c.auxiliaryHead]?} 0 result := by
  cases action : R.transition c.state none certificate[c.auxiliaryHead]?
      (if c.indexHead < n then some () else none) (c.work c.workHead) with
  | accept =>
      have equal : result = .accepted c.output := by simpa [Machine.observe, generatorData, action] using terminal.symm
      subst result
      apply TransducerBank.TapeBank.Executes.accept
      simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
        compositionSelect, compositionTransition, action]
  | reject =>
      have equal : result = .rejected := by simpa [Machine.observe, generatorData, action] using terminal.symm
      subst result
      apply TransducerBank.TapeBank.Executes.reject
      simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
        compositionSelect, compositionTransition, action]
  | step state write work input auxiliary index emit => simp [Machine.observe, generatorData, action] at terminal
  | readRandom no yes =>
      have unavailable : ¬c.randomHead < bits.length := by
        by_contra available
        simp [Machine.observe, generatorData, action, available] at terminal
      have equal : result = .exhausted := by simpa [Machine.observe, generatorData, action, unavailable] using terminal.symm
      subst result
      apply TransducerBank.TapeBank.Executes.exhausted _ (.recover no) (.recover yes)
      · simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
          compositionSelect, compositionTransition, action]
      · exact List.getElem?_eq_none (by change bits.length ≤ c.randomHead; omega)

theorem composition_recoverer_executes (n : ℕ) (certificate bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (c : Configuration R)
    (t : ℕ) (result : Outcome α) (source : R.runFrom (generatorData n certificate) bits c t = .halted result)
    (indexBound : c.indexHead ≤ n) (auxiliaryBound : c.auxiliaryHead ≤ certificate.length) :
    ∃ ticks, ticks ≤ 5 * t + 2 ∧ (samplerCompositionBank S R).Executes (generatorData n) bits
      (recovererBankConfiguration S R n certificate samplerWork samplerHead c) ticks result := by
  obtain ⟨terminal, ticks, bound, path, halted, _, _⟩ :=
    composition_recoverer_runFrom S R n certificate bits samplerWork samplerHead c t result source indexBound auxiliaryBound
  exact ⟨ticks, bound, by simpa using path.executes _ (composition_recoverer_terminal S R n certificate bits samplerWork samplerHead terminal result halted)⟩

end
end ComplexityOfGenerators.Simulation
