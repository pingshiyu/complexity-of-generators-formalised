import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Completeness

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

open Simulation.TransducerBank.UpToGeneration

/-- Exact cumulative support of the one real finite generator program. -/
theorem upTo_generated_prefix (language : Language α) (source : MultitapeMachine α Bool Unit)
    (fallback : Word α)
    (termination : ∀ word, ∃ time, source.TimeBound (decisionData word) time)
    (recognizes : ∀ word, (∃ bits, source.Accepts (decisionData word) bits) ↔ word ∈ language)
    (fallbackMember : fallback ∈ language) (shortest : ∀ word ∈ language, fallback.length ≤ word.length)
    (n : ℕ) :
    (machine source fallback).generatedLanguage (generatorData n) =
      {word | word ∈ language ∧ word.length ≤ n} := by
  have finite : ∀ word, source.Terminates (decisionData word) := by
    intro word bits
    obtain ⟨time, bounded⟩ := termination word
    obtain ⟨ticks, result, _, execution⟩ := bounded bits
    exact ⟨ticks, result, execution⟩
  ext word
  exact ⟨generated_sound source fallback language finite recognizes fallbackMember n word,
    fun member => generated_complete source fallback language recognizes shortest n word member.1 member.2⟩

/-- The only machine field is the actual proposal/source/fallback controller.
Language and termination arguments supply proof fields, never operations in its
finite transition table. -/
def upToFamily (language : Language α) (source : MultitapeMachine α Bool Unit) (fallback : Word α)
    (termination : ∀ word, ∃ time, source.TimeBound (decisionData word) time)
    (recognizes : ∀ word, (∃ bits, source.Accepts (decisionData word) bits) ↔ word ∈ language)
    (fallbackMember : fallback ∈ language) (shortest : ∀ word ∈ language, fallback.length ≤ word.length) :
    UpToGeneratorFamily α := by
  let uniform : UniformGenerators α :=
    ⟨machine source fallback, machine_isGenerator source fallback termination⟩
  have layers (n : ℕ) : uniform.layer n = {word | word ∈ language ∧ word.length ≤ n} :=
    upTo_generated_prefix language source fallback termination recognizes fallbackMember shortest n
  have same : uniform.language = language := by
    ext word
    change (∃ n, word ∈ uniform.layer n) ↔ word ∈ language
    simp only [layers]
    exact ⟨fun ⟨_, member, _⟩ => member, fun member => ⟨word.length, member, Nat.le_refl _⟩⟩
  exact {toUniformGenerators := uniform, prefixLanguage := fun n => by rw [layers, same]}

theorem upToFamily_language (language : Language α) (source : MultitapeMachine α Bool Unit) (fallback : Word α)
    (termination : ∀ word, ∃ time, source.TimeBound (decisionData word) time)
    (recognizes : ∀ word, (∃ bits, source.Accepts (decisionData word) bits) ↔ word ∈ language)
    (fallbackMember : fallback ∈ language) (shortest : ∀ word ∈ language, fallback.length ≤ word.length) :
    (upToFamily language source fallback termination recognizes fallbackMember shortest).toUniformGenerators.language = language := by
  ext word
  change (∃ n, word ∈ (machine source fallback).generatedLanguage (generatorData n)) ↔ word ∈ language
  simp only [upTo_generated_prefix language source fallback termination recognizes fallbackMember shortest]
  exact ⟨fun ⟨_, member, _⟩ => member, fun member => ⟨word.length, member, Nat.le_refl _⟩⟩

end
end ComplexityOfGenerators.Multitape
