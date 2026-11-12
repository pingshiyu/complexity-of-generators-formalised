import ComplexityOfGenerators.Simulation.CompositionDecisionSpace
import ComplexityOfGenerators.Simulation.FixedFallbackSemantics
import ComplexityOfGenerators.Simulation.FiniteUpToWordSampler
import ComplexityOfGenerators.Simulation.TransducerBank.RegionEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.RegionDrain

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (S : Machine Unit Bool α) (D : Machine α Bool Unit) (fallback : List α)

omit [Fintype α] in
theorem fixedFallback_source_region {n : ℕ} {bits : BitString}
    {c d : CompositionConfiguration S (auxiliaryDecision D)} {r t : ℕ}
    (path : (samplerCompositionBank S (auxiliaryDecision D)).RegionSteps (generatorData n) bits r c t d) :
    (fixedFallbackBank S D fallback).RegionSteps (generatorData n) bits r
      (c.mapState FixedFallbackPhase.source) t (d.mapState FixedFallbackPhase.source) := by
  apply TransducerBank.TapeBank.RegionSteps.mapState _ _ FixedFallbackPhase.source (fun _ => rfl) ?_ ?_ path
  · intro q i a x origin cell next write work input auxiliary index emit table
    change compositionTransition S (auxiliaryDecision D) q x origin cell = _ at table
    simp only [fixedFallbackBank, fixedFallbackTransition, table, fixedFallbackSourceInstruction]
  · intro q i a x origin cell no yes table
    change compositionTransition S (auxiliaryDecision D) q x origin cell = _ at table
    simp only [fixedFallbackBank, fixedFallbackTransition, table, fixedFallbackSourceInstruction]

omit [Fintype α] in
theorem fixedFallback_below_inRegion (n : ℕ) (bits : BitString) (below : n < fallback.length) :
    (fixedFallbackBank S D fallback).RegionRun (generatorData n) bits (n + 1)
      (fixedFallbackBank S D fallback).initialConfiguration .exhausted := by
  let B := fixedFallbackBank S D fallback
  let c := fixedFallbackGuardConfiguration S D fallback .drain n
  have path := (fixedFallback_below_steps S D fallback n bits below).inRegion B 0 (B.initial_bounded _)
  have bounded : B.Bounded (generatorData n) (n + 1) c := by simpa [c] using path.end_bound B
  have rest := TransducerBank.TapeBank.drain_inRegion B (generatorData n) bits .drain
    (by intros; rfl) bits.length c rfl
    (by simp [c, fixedFallbackGuardConfiguration, TransducerBank.TapeBank.initialConfiguration])
    (n + 1) bounded
  exact rest.prepend B (by simpa using path)

def fixedFallbackRadius (n sampleTime space fallbackLength : ℕ) : ℕ :=
  20 * (n + sampleTime + space + fallbackLength + 1)

theorem fixedFallback_live_inRegion (deterministic : D.Deterministic)
    (n sampleTime s : ℕ) (bits : BitString) (live : fallback.length ≤ n)
    (sampling : ∀ bits, ∃ result, S.run (generatorData n) bits sampleTime = .halted result ∧
      (match result with | .accepted word => word.length ≤ n | .rejected => False | .exhausted => True))
    (halts : ∀ word : List α, word.length ≤ n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length ≤ n → D.SpaceBound (decisionData word) s) :
    ∃ result, (fixedFallbackBank S D fallback).RegionRun (generatorData n) bits
      (fixedFallbackRadius n sampleTime s fallback.length)
      (fixedFallbackBank S D fallback).initialConfiguration result := by
  let B := fixedFallbackBank S D fallback
  let R := auxiliaryDecision D
  let C := samplerCompositionBank S R
  let radius := fixedFallbackRadius n sampleTime s fallback.length
  obtain ⟨sampleResult, source, related⟩ := sampling bits
  cases sampleResult with
  | rejected => exact False.elim related
  | exhausted =>
      obtain ⟨terminal, ticks, cost, path, halted, _, _, _⟩ :=
        composition_sampler_prefix S R n bits sampleTime .exhausted source
      obtain ⟨failureTicks, failureCost, failure⟩ := composition_sampler_failure S R n bits terminal .exhausted halted (by intros; simp)
      have initial := (fixedFallback_boot S D fallback n bits live).trans B (fixedFallback_source_path S D fallback path)
      have execution := initial.executes B (fixedFallback_source_exhausted S D fallback failure)
      have short : bits.length ≤ sampleTime := by
        by_contra contrary
        exact S.run_not_exhausted_of_length _ bits sampleTime (by omega) source
      refine ⟨.exhausted, (execution.inRegion B (B.initial_bounded _)).mono B ?_⟩
      unfold fixedFallbackRadius
      omega
  | accepted word =>
      obtain ⟨sampled, samplingTicks, samplingCost, samplePath, sampledTerminal, indexBound, _, _⟩ :=
        composition_sampler_prefix S R n bits sampleTime (.accepted word) source
      obtain ⟨action, output⟩ := S.accepting_observation sampledTerminal
      have handoff := composition_handoff S R n bits sampled (by simpa [generatorData] using action)
      rw [output] at handoff
      have entered := (fixedFallback_boot S D fallback n bits live).trans B
        (fixedFallback_source_path S D fallback (samplePath.trans C handoff))
      let before := 2 * fallback.length + 2 + (samplingTicks + (sampled.indexHead + word.length + 3))
      have prefixRegion : B.RegionSteps (generatorData n) bits before B.initialConfiguration before
          ((recovererBankConfiguration S R n word sampled.work sampled.workHead
            {R.initialConfiguration with randomHead := sampled.randomHead}).mapState FixedFallbackPhase.source) := by
        simpa [before] using entered.inRegion B 0 (B.initial_bounded _)
      have samplerHead : sampled.workHead.natAbs ≤ before := by
        have bound := (prefixRegion.end_bound B).head 0
        simpa [TransducerBank.BankConfiguration.mapState, recovererBankConfiguration] using bound
      obtain ⟨clock, result, nativeHalted⟩ := halts word related
      obtain ⟨ticks, _, terminal, decisionPath, observation⟩ := D.runFrom_path (decisionData word) [] D.initialConfiguration clock
      rw [Machine.runFrom_initial, nativeHalted] at observation
      have nativeBounds := (space word related).steps_decisionView_bounded D decisionPath
      have inputBound : terminal.inputHead ≤ word.length := nativeBounds.inputHead
      have workBound : terminal.workHead.natAbs ≤ s := nativeBounds.workHead
      have decision := compositionDecision_steps_inRegion S D deterministic n word bits sampled.work sampled.workHead
        sampled.randomHead s (space word related) decisionPath
      let terminalR := auxiliaryDecisionAt D sampled.randomHead terminal
      let base := n + word.length + sampled.workHead.natAbs + s
      have fetch := (composition_recoverer_fetch S R n word bits sampled.work sampled.workHead terminalR).inRegion C base
        (compositionDecision_bounded S D n word sampled.work sampled.workHead sampled.randomHead s terminal inputBound workBound)
      have wholeDecision := decision.trans C (fetch.mono C (by omega : base + 2 ≤ base + 5))
      have adaptedDecision := fixedFallback_source_region S D fallback wholeDecision
      have entryEq : auxiliaryDecisionAt D sampled.randomHead D.initialConfiguration =
          {R.initialConfiguration with randomHead := sampled.randomHead} := by
        rfl
      rw [entryEq] at adaptedDecision
      have small : before ≤ radius := by unfold before radius fixedFallbackRadius; omega
      have decisionSmall : base + 5 ≤ radius := by unfold base radius fixedFallbackRadius; omega
      have finalBound := adaptedDecision.end_bound B
      cases terminalAction : D.transition terminal.state word[terminal.inputHead]? none none (terminal.work terminal.workHead) with
      | readRandom no yes =>
          have impossible := deterministic terminal.state word[terminal.inputHead]? none none (terminal.work terminal.workHead)
          simp [terminalAction] at impossible
      | step => simp [Machine.observe, decisionData, terminalAction] at observation
      | accept =>
          have accepted : R.observe (certificateData n word) bits terminalR = .halted (.accepted []) := by
            simp [R, Machine.observe, terminalR, auxiliaryDecisionAt, auxiliaryDecisionConfiguration,
              auxiliaryDecision, certificateData, terminalAction]
          have finish := fixedFallback_finish_accept S D fallback n bits word sampled.work sampled.workHead terminalR
            accepted rfl (by simpa [terminalR, auxiliaryDecisionAt, auxiliaryDecisionConfiguration] using inputBound)
          have tail := (finish.inRegion B finalBound).mono B (s := radius)
            (by simp only [radius, fixedFallbackRadius, terminalR, auxiliaryDecisionAt, auxiliaryDecisionConfiguration]; omega)
          exact ⟨.accepted word, (tail.prepend B (adaptedDecision.mono B decisionSmall)).prepend B (prefixRegion.mono B small)⟩
      | reject =>
          have rejected : R.observe (certificateData n word) bits terminalR = .halted .rejected := by
            simp [R, Machine.observe, terminalR, auxiliaryDecisionAt, auxiliaryDecisionConfiguration,
              auxiliaryDecision, certificateData, terminalAction]
          have finish := fixedFallback_finish_reject S D fallback n bits word sampled.work sampled.workHead terminalR rejected rfl
          have tail := (finish.inRegion B finalBound).mono B (s := radius)
            (by simp only [radius, fixedFallbackRadius]; omega)
          exact ⟨.accepted fallback, (tail.prepend B (adaptedDecision.mono B decisionSmall)).prepend B (prefixRegion.mono B small)⟩

/-- The native compiler's physical region remains bounded independently of
the decision branch's running time and the supplied random-tape length. -/
theorem fixedFallback_spaceBound (deterministic : D.Deterministic)
    (n sampleTime s : ℕ)
    (sampling : ∀ bits, ∃ result, S.run (generatorData n) bits sampleTime = .halted result ∧
      (match result with | .accepted word => word.length ≤ n | .rejected => False | .exhausted => True))
    (halts : ∀ word : List α, word.length ≤ n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length ≤ n → D.SpaceBound (decisionData word) s) :
    (fixedFallbackGenerator S D fallback).SpaceBound (generatorData n)
      (2 * fixedFallbackRadius n sampleTime s fallback.length + 1) := by
  let B := fixedFallbackBank S D fallback
  let radius := fixedFallbackRadius n sampleTime s fallback.length
  apply Machine.spaceBound_of_terminal_paths
  intro bits
  have run : ∃ result, B.RegionRun (generatorData n) bits radius B.initialConfiguration result := by
    by_cases live : fallback.length ≤ n
    · exact fixedFallback_live_inRegion S D fallback deterministic n sampleTime s bits live sampling halts space
    · refine ⟨.exhausted, (fixedFallback_below_inRegion S D fallback n bits (by omega)).mono B ?_⟩
      unfold radius fixedFallbackRadius
      omega
  obtain ⟨result, run⟩ := run
  obtain ⟨ready, related, boot, region⟩ := TransducerBank.bank_loaded_inRegion B (generatorData n) bits radius
  obtain ⟨ticks, finish, path, terminal, visited⟩ := run.compile B (fun _ => false) ready related region
  exact ⟨1 + ticks, finish, result, boot.trans _ path, terminal, visited.card_le _⟩

end
end ComplexityOfGenerators.Simulation
