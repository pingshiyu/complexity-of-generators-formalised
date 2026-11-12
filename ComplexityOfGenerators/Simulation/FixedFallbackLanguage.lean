import ComplexityOfGenerators.Simulation.FixedFallbackExecution
import ComplexityOfGenerators.Foundations.LanguageClosure

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (S : Machine Unit Bool α) (M : Machine α Bool Unit) (fallback : List α)

def fixedFallbackGenerator : Machine Unit Bool α := TransducerBank.bankMachine (fixedFallbackBank S M fallback)

/-- Join a sampling witness to a specified decision branch at the consumed
random cursor. No unconsumed sampling bits are passed to the decider. -/
theorem fixedFallback_branch (n : ℕ) (word : List α) (choices : BitString) (sampled : word ∈ S.generatedLanguage (generatorData n))
    (live : fallback.length ≤ n) (positive : 0 < choices.length)
    (t : ℕ) (result : Outcome Unit) (decision : M.run (decisionData word) choices t = .halted result) :
    ∃ bits ticks, 0 < bits.length ∧ (fixedFallbackGenerator S M fallback).run (generatorData n) bits ticks =
      .halted (fixedFallbackOutcome word fallback result) := by
  let R := auxiliaryDecision M
  obtain ⟨samplingBits, _, samplingTime, source⟩ := sampled
  obtain ⟨terminal, ticks, _, path, halted, indexBound, randomBound, _⟩ :=
    composition_sampler_prefix S R n samplingBits samplingTime (.accepted word) source
  obtain ⟨action, output⟩ := S.accepting_observation halted
  let bits := samplingBits.take terminal.randomHead ++ choices
  have path' := path.replace_suffix (samplerCompositionBank S R) randomBound choices
  have sampled' : S.observe (generatorData n) bits terminal = .halted (.accepted word) := by
    simp only [Machine.observe, action, output]
  have randomBound' : terminal.randomHead ≤ bits.length := by
    simp [bits, List.length_take, Nat.min_eq_left randomBound]
  have drop : bits.drop terminal.randomHead = choices := by
    simp [bits, List.drop_append, List.length_take, Nat.min_eq_left randomBound]
  obtain ⟨total, _, execution⟩ := fixedFallback_after_sample S M fallback n bits word live terminal ticks path' sampled'
    indexBound randomBound' t result (by rw [drop]; exact decision)
  obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (fixedFallbackBank S M fallback) _ bits total _ execution
  exact ⟨bits, nativeTicks, by simp [bits, positive], native⟩

theorem fixedFallback_contains_np_word (n : ℕ) (word : List α) (sampled : word ∈ S.generatedLanguage (generatorData n))
    (live : fallback.length ≤ n) (member : ∃ choices, M.Accepts (decisionData word) choices) :
    word ∈ (fixedFallbackGenerator S M fallback).generatedLanguage (generatorData n) := by
  obtain ⟨choices, out, t, accepted⟩ := member
  have appended := M.produces_append (decisionData word) choices [false] out ⟨t, accepted⟩
  obtain ⟨t', accepted'⟩ := appended
  obtain ⟨bits, ticks, positive, native⟩ := fixedFallback_branch S M fallback n word (choices ++ [false]) sampled live
    (by simp) t' (.accepted out) accepted'
  exact ⟨bits, List.ne_nil_of_length_pos positive, ticks, native⟩


end
end ComplexityOfGenerators.Simulation
