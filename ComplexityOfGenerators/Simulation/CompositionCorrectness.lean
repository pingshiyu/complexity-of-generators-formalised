import ComplexityOfGenerators.Simulation.CompositionExecution
import ComplexityOfGenerators.Foundations.BoundedGeneration
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

def samplerComposition : Machine Unit Bool α := TransducerBank.bankMachine (samplerCompositionBank S R)

def CompositionOutcome (n : ℕ) : Outcome α → Prop
  | .accepted word => ∃ certificate, certificate ∈ S.generatedLanguage (generatorData n) ∧
      word ∈ R.generatedLanguage (generatorData n certificate)
  | .rejected => ∃ certificate, certificate ∈ S.generatedLanguage (generatorData n) ∧
      ∃ bits t, R.run (generatorData n certificate) bits t = .halted .rejected
  | .exhausted => True

/-- Total finite-bank execution and support preservation. Explicit failure of
the first stage drains the tape; explicit failure of the second stage can only
be inherited from a genuine recovery call on a sampled certificate. -/
theorem composition_executes (n sampleTime recoveryTime : ℕ) (bits : BitString)
    (sample : S.TimeBound (generatorData n) sampleTime)
    (recover : ∀ certificate, certificate ∈ S.generatedLanguage (generatorData n) →
      R.TimeBound (generatorData n certificate) recoveryTime) :
    ∃ ticks result, ticks ≤ 3 * n + 5 * sampleTime + 5 * recoveryTime + bits.length + 10 ∧
      (samplerCompositionBank S R).Executes (generatorData n) bits (samplerCompositionBank S R).initialConfiguration ticks result ∧
      CompositionOutcome S R n result := by
  obtain ⟨result, source⟩ := sample bits
  obtain ⟨terminal, ticks, cost, path, halted, indexBound, randomBound, _⟩ :=
    composition_sampler_prefix S R n bits sampleTime result source
  cases result with
  | accepted certificate =>
      obtain ⟨action, output⟩ := S.accepting_observation halted
      have sampled : certificate ∈ S.generatedLanguage (generatorData n) :=
        ⟨bits ++ [false], by simp, S.produces_append _ bits [false] certificate ⟨sampleTime, source⟩⟩
      have length := S.accepted_output_length_le _ bits sampleTime certificate source
      obtain ⟨result, recovered⟩ := recover certificate sampled (bits.drop terminal.randomHead)
      have shifted := R.runFrom_drop_random (generatorData n certificate) bits terminal.randomHead recoveryTime randomBound
      rw [recovered] at shifted
      have handoff := composition_handoff S R n bits terminal (by simpa [generatorData] using action)
      rw [output] at handoff
      obtain ⟨recoveryTicks, recoveryCost, execution⟩ := composition_recoverer_executes S R n certificate bits
        terminal.work terminal.workHead {R.initialConfiguration with randomHead := terminal.randomHead}
        recoveryTime result shifted (Nat.zero_le _) (Nat.zero_le _)
      refine ⟨ticks + (terminal.indexHead + certificate.length + 3) + recoveryTicks, result, by omega,
        (path.trans _ handoff).executes _ execution, ?_⟩
      cases result with
      | accepted word =>
          exact ⟨certificate, sampled, bits.drop terminal.randomHead ++ [false], by simp,
            R.produces_append _ _ [false] word ⟨recoveryTime, recovered⟩⟩
      | rejected => exact ⟨certificate, sampled, bits.drop terminal.randomHead, recoveryTime, recovered⟩
      | exhausted => trivial
  | rejected =>
      obtain ⟨failureTicks, failureCost, execution⟩ := composition_sampler_failure S R n bits terminal .rejected halted (by intros; simp)
      exact ⟨ticks + failureTicks, .exhausted, by omega, path.executes _ execution, trivial⟩
  | exhausted =>
      obtain ⟨failureTicks, failureCost, execution⟩ := composition_sampler_failure S R n bits terminal .exhausted halted (by intros; simp)
      exact ⟨ticks + failureTicks, .exhausted, by omega, path.executes _ execution, trivial⟩

/-- On sufficiently long tapes, an accepting sampling trial leaves enough
randomness for a bounded genuine recovery generator. -/
theorem composition_accepts_long (n sampleTime recoveryTime : ℕ) (bits : BitString)
    (sample : S.TimeBound (generatorData n) sampleTime) (accepted : S.Accepts (generatorData n) bits)
    (recover : ∀ certificate, certificate ∈ S.generatedLanguage (generatorData n) →
      R.IsGenerator (generatorData n certificate) ∧ R.TimeBound (generatorData n certificate) recoveryTime)
    (long : 2 * n + 4 * sampleTime + recoveryTime + 3 < bits.length) :
    (samplerComposition S R).Accepts (generatorData n) bits := by
  obtain ⟨certificate, produced⟩ := accepted
  have source := S.produces_at_bound _ bits sampleTime certificate (sample bits) produced
  obtain ⟨terminal, ticks, cost, path, halted, _, randomBound, consumed⟩ :=
    composition_sampler_prefix S R n bits sampleTime (.accepted certificate) source
  obtain ⟨action, output⟩ := S.accepting_observation halted
  have sampled : certificate ∈ S.generatedLanguage (generatorData n) :=
    ⟨bits ++ [false], by simp, S.produces_append _ bits [false] certificate produced⟩
  obtain ⟨word, recovered⟩ := R.accepts_at_timeBound_of_long_tape _ recoveryTime
    (recover certificate sampled).1 (recover certificate sampled).2 (bits.drop terminal.randomHead)
    (by simp only [List.length_drop]; omega)
  have shifted := R.runFrom_drop_random (generatorData n certificate) bits terminal.randomHead recoveryTime randomBound
  rw [recovered] at shifted
  have handoff := composition_handoff S R n bits terminal (by simpa [generatorData] using action)
  rw [output] at handoff
  obtain ⟨recoveryTicks, _, execution⟩ := composition_recoverer_executes S R n certificate bits
    terminal.work terminal.workHead {R.initialConfiguration with randomHead := terminal.randomHead}
    recoveryTime (.accepted word) shifted (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (samplerCompositionBank S R) _ bits _ _
    ((path.trans _ handoff).executes _ execution)
  exact ⟨word, nativeTicks, native⟩

end
end ComplexityOfGenerators.Simulation
