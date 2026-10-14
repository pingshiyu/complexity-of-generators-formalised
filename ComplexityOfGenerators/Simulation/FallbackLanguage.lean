import ComplexityOfGenerators.Simulation.FallbackExecution
import ComplexityOfGenerators.Foundations.LanguageClosure

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Unit) (bit allowEmpty : Bool)

def fallbackGenerator : Machine Unit Bool Bool := TransducerBank.bankMachine (fallbackBank M bit allowEmpty)

/-- Join a sampling witness to a specified decision branch at the consumed
random cursor. No unconsumed sampling bits are passed to the decider. -/
theorem fallback_branch (n : ℕ) (word choices : BitString) (length : word.length = n)
    (live : n ≠ 0 ∨ allowEmpty = true) (positive : 0 < choices.length)
    (t : ℕ) (result : Outcome Unit) (decision : M.run (decisionData word) choices t = .halted result) :
    ∃ bits ticks, 0 < bits.length ∧ (fallbackGenerator M bit allowEmpty).run (generatorData n) bits ticks =
      .halted (fallbackOutcome word bit result) := by
  let R := auxiliaryDecision M
  let samplingBits := word ++ [false]
  have source : wordSampler.run (generatorData n) samplingBits (2 * n) = .halted (.accepted word) := by
    rw [wordSampler_run]
    simp [samplingBits, wordSamplerOutcome, ← length, List.take_append]
  obtain ⟨terminal, ticks, _, path, halted, indexBound, randomBound, _⟩ :=
    composition_sampler_prefix wordSampler R n samplingBits (2 * n) (.accepted word) source
  obtain ⟨action, output⟩ := wordSampler.accepting_observation halted
  let bits := samplingBits.take terminal.randomHead ++ choices
  have path' := path.replace_suffix (samplerCompositionBank wordSampler R) randomBound choices
  have sampled' : wordSampler.observe (generatorData n) bits terminal = .halted (.accepted word) := by
    simp only [Machine.observe, action, output]
  have randomBound' : terminal.randomHead ≤ bits.length := by
    simp [bits, List.length_take, Nat.min_eq_left randomBound]
  have drop : bits.drop terminal.randomHead = choices := by
    simp [bits, List.drop_append, List.length_take, Nat.min_eq_left randomBound]
  obtain ⟨total, _, execution⟩ := fallback_after_sample M bit allowEmpty n bits word live terminal ticks path' sampled'
    indexBound randomBound' t result (by rw [drop]; exact decision)
  obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (fallbackBank M bit allowEmpty) _ bits total _ execution
  exact ⟨bits, nativeTicks, by simp [bits, positive], native⟩

theorem fallback_contains_np_word (n : ℕ) (word : BitString) (length : word.length = n)
    (live : n ≠ 0 ∨ allowEmpty = true) (member : ∃ choices, M.Accepts (decisionData word) choices) :
    word ∈ (fallbackGenerator M bit allowEmpty).generatedLanguage (generatorData n) := by
  obtain ⟨choices, out, t, accepted⟩ := member
  have appended := M.produces_append (decisionData word) choices [false] out ⟨t, accepted⟩
  obtain ⟨t', accepted'⟩ := appended
  obtain ⟨bits, ticks, positive, native⟩ := fallback_branch M bit allowEmpty n word (choices ++ [false]) length live
    (by simp) t' (.accepted out) accepted'
  exact ⟨bits, List.ne_nil_of_length_pos positive, ticks, native⟩

theorem fallback_contains_constant (n t : ℕ) (nonzero : n ≠ 0)
    (time : M.TimeBound (decisionData (List.replicate n bit)) t) :
    List.replicate n bit ∈ (fallbackGenerator M bit allowEmpty).generatedLanguage (generatorData n) := by
  let choices := List.replicate (t + 1) false
  obtain ⟨result, decision⟩ := time choices
  have notExhausted : result ≠ .exhausted := by
    intro equal
    subst result
    exact M.run_not_exhausted_of_length _ choices t (by simp [choices]) decision
  obtain ⟨bits, ticks, positive, native⟩ := fallback_branch M bit allowEmpty n (List.replicate n bit) choices
    (by simp) (Or.inl nonzero) (by simp [choices]) t result decision
  refine ⟨bits, List.ne_nil_of_length_pos positive, ticks, ?_⟩
  cases result with
  | accepted out => exact native
  | rejected => simpa [fallbackOutcome] using native
  | exhausted => exact False.elim (notExhausted rfl)

end
end ComplexityOfGenerators.Simulation
