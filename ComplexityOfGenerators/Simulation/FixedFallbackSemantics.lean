import ComplexityOfGenerators.Simulation.FixedFallbackLanguage
import ComplexityOfGenerators.Proofs.GeneratorCriteria

/-! Support and productivity of the fixed-fallback machine use finite bounds
for each index, without requiring that those bounds be computable or polynomial.
The finite control table does not depend on either bound. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (S : Machine Unit Bool α) (D : Machine α Bool Unit)
  (fallback : List α) (L : Language α) (n sampleTime decisionTime : ℕ)
  (sampling : ∀ bits, ∃ result, S.run (generatorData n) bits sampleTime = .halted result ∧
    (match result with | .accepted word => word.length ≤ n | .rejected => False | .exhausted => True))
  (sampleSupport : ∀ word, word.length ≤ n → word ∈ S.generatedLanguage (generatorData n))
  (time : ∀ word : List α, word.length ≤ n → D.TimeBound (decisionData word) decisionTime)
  (language : ∀ word, (∃ bits, D.Accepts (decisionData word) bits) ↔ word ∈ L)
  (member : fallback ∈ L) (shortest : ∀ word ∈ L, fallback.length ≤ word.length)

include sampling sampleSupport time language member shortest

theorem fixedFallback_support :
    (fixedFallbackGenerator S D fallback).generatedLanguage (generatorData n) =
      {word | word ∈ L ∧ word.length ≤ n} := by
  ext word
  constructor
  · rintro ⟨bits, _, ticks, accepted⟩
    by_cases live : fallback.length ≤ n
    · obtain ⟨bankTicks, result, _, execution, related⟩ :=
        fixedFallback_executes_live S D fallback n sampleTime decisionTime bits live sampling time
      obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run
        (fixedFallbackBank S D fallback) _ bits bankTicks result execution
      have same := (fixedFallbackGenerator S D fallback).halted_outcome_unique _ bits ticks nativeTicks _ _ accepted native
      subst result
      rcases related with ⟨length, accepts⟩ | rfl
      · exact ⟨(language word).mp accepts, length⟩
      · exact ⟨member, live⟩
    · obtain ⟨bankTicks, _, execution⟩ := fixedFallback_executes_below S D fallback n bits (by omega)
      obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run
        (fixedFallbackBank S D fallback) _ bits bankTicks .exhausted execution
      have same := (fixedFallbackGenerator S D fallback).halted_outcome_unique _ bits ticks nativeTicks _ _ accepted native
      cases same
  · rintro ⟨wordMember, length⟩
    exact fixedFallback_contains_np_word S D fallback n word (sampleSupport word length)
      ((shortest word wordMember).trans length) ((language word).mpr wordMember)

theorem fixedFallback_isGenerator :
    (fixedFallbackGenerator S D fallback).IsGenerator (generatorData n) := by
  let G := fixedFallbackGenerator S D fallback
  have finite (bits : BitString) : ∃ ticks result, G.run (generatorData n) bits ticks = .halted result ∧
      (match result with
        | .accepted _ => True
        | .rejected => False
        | .exhausted => n < fallback.length ∨ bits.length ≤ 2 * n + 4 * sampleTime + decisionTime + 3) := by
    by_cases live : fallback.length ≤ n
    · obtain ⟨ticks, result, _, execution, related⟩ :=
        fixedFallback_executes_live S D fallback n sampleTime decisionTime bits live sampling time
      obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (fixedFallbackBank S D fallback) _ bits ticks result execution
      refine ⟨nativeTicks, result, native, ?_⟩
      cases result with
      | accepted _ => trivial
      | rejected => exact related
      | exhausted => exact Or.inr related
    · obtain ⟨ticks, _, execution⟩ := fixedFallback_executes_below S D fallback n bits (by omega)
      obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (fixedFallbackBank S D fallback) _ bits ticks .exhausted execution
      exact ⟨nativeTicks, .exhausted, native, Or.inl (by omega)⟩
  apply Machine.isGenerator_of_full_trials _ _ (2 * n + 4 * sampleTime + decisionTime + 4)
  · constructor
    · intro bits
      obtain ⟨ticks, result, execution, _⟩ := finite bits
      exact ⟨ticks, result, execution⟩
    · intro bits ticks rejected
      obtain ⟨otherTicks, result, execution, related⟩ := finite bits
      have same := G.halted_outcome_unique _ bits ticks otherTicks _ _ rejected execution
      subst result
      exact related
  · intro bits length
    constructor
    · intro accepted
      exact (G.generatedLanguage_nonempty_iff_accepts _).mpr ⟨bits, accepted⟩
    · intro nonempty
      change (G.generatedLanguage (generatorData n)).Nonempty at nonempty
      rw [fixedFallback_support S D fallback L n sampleTime decisionTime sampling sampleSupport time language member shortest] at nonempty
      obtain ⟨word, wordMember, bound⟩ := nonempty
      have live := (shortest word wordMember).trans bound
      obtain ⟨ticks, result, execution, related⟩ := finite bits
      cases result with
      | accepted word => exact ⟨word, ticks, execution⟩
      | rejected => exact False.elim related
      | exhausted => rcases related with below | short <;> omega

end
end ComplexityOfGenerators.Simulation
