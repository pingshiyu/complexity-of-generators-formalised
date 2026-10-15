import ComplexityOfGenerators.Simulation.CyclicGenerator.Generation
import ComplexityOfGenerators.Proofs.EmptyWordGeneration
import ComplexityOfGenerators.Foundations.StationarySpace

/-! The reverse inclusion in Theorem 6.1, following Appendix A.17: enumerate
words, run the space-bounded decider, and repeatedly offer accepted words with
probability one half. The concrete compiler's visited-cell bound is used here. -/

namespace ComplexityOfGenerators

noncomputable section

variable {α : Type} [Fintype α]

theorem mem_pspaceg_of_lengthSlices (L : Language α) (M : Machine Unit Bool α)
    (space : PolynomialBound) (generator : ∀ n, M.IsGenerator (generatorData n))
    (slices : ∀ n, M.generatedLanguage (generatorData n) = lengthSlice L n)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n)) : L ∈ PSPACEG α := by
  let G : GeneratorFamily α := {
    machine := M
    isGenerator := generator
    outputLength := by
      intro n word member
      change word ∈ M.generatedLanguage (generatorData n) at member
      rw [slices n] at member
      exact member.2 }
  refine ⟨G, ?_, space, bounded⟩
  ext word
  change (∃ n, word ∈ M.generatedLanguage (generatorData n)) ↔ word ∈ L
  simp only [slices]
  exact ⟨fun ⟨_, member, _⟩ => member, fun member => ⟨word.length, member, rfl⟩⟩

theorem empty_language_in_pspaceg : (∅ : Language α) ∈ PSPACEG α := by
  let one : PolynomialBound := ⟨1, 0, by decide⟩
  have noAccepts : ∀ n bits, ¬(emptyGenerator α).Accepts (generatorData n) bits := by
    rintro n bits ⟨word, t, accepted⟩
    rw [emptyGenerator_run] at accepted
    split_ifs at accepted <;> cases accepted
  apply mem_pspaceg_of_lengthSlices ∅ (emptyGenerator α) one
  · intro n
    have emptyEvent : (emptyGenerator α).acceptedStreams (generatorData n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro stream ⟨bits, _, accepted⟩
      exact noAccepts n bits accepted
    refine ⟨⟨?_, ?_⟩, Or.inr ?_⟩
    · intro bits
      exact ⟨bits.length, .exhausted, by simp [emptyGenerator_run]⟩
    · intro bits t
      rw [emptyGenerator_run]
      split_ifs <;> simp
    · simp [emptyEvent]
  · intro n
    ext word
    simp only [lengthSlice, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, iff_false]
    rintro ⟨bits, _, produced⟩
    exact noAccepts n bits ⟨word, produced⟩
  · intro n
    have stationary : (emptyGenerator α).StationaryWork := by
      intro q input auxiliary index cell
      trivial
    simpa [one, PolynomialBound.eval] using stationary.spaceBound _ (generatorData n)

theorem empty_word_language_in_pspaceg : ({[]} : Language α) ∈ PSPACEG α := by
  let one : PolynomialBound := ⟨1, 0, by decide⟩
  apply mem_pspaceg_of_lengthSlices {[]} (emptyWordGenerator α) one
  · exact emptyWordGenerator_isGenerator α
  · intro n
    rw [emptyWordGenerator_language]
    ext word
    by_cases zero : n = 0 <;> simp [zero, lengthSlice]
    rintro rfl
    simpa [eq_comm] using zero
  · intro n
    have stationary : (emptyWordGenerator α).StationaryWork := by
      intro q input auxiliary index cell
      cases index <;> trivial
    simpa [one, PolynomialBound.eval] using stationary.spaceBound _ (generatorData n)

open Simulation.CyclicGenerator in
theorem pspace_subset_pspaceg_of_nonempty [Nonempty α] : PSPACE α ⊆ PSPACEG α := by
  rintro L ⟨D, space, deterministic, halts, bounded, language⟩
  let first : α := alphabet.symm ⟨0, Fintype.card_pos⟩
  have least : firstLetter = some first := by simp [firstLetter, first, Fintype.card_pos]
  let polynomial : Polynomial ℕ := 10 * (Polynomial.X + space.asPolynomial + 1) + 1
  let generatorSpace := PolynomialBound.ofPolynomial polynomial
  apply mem_pspaceg_of_lengthSlices L (machine D) generatorSpace
  · intro n
    exact machine_isGenerator D first least deterministic n (space n) (fun word _ => halts word)
      (fun word length => length ▸ bounded word)
  · intro n
    exact machine_language D first least deterministic n (space n) (fun word _ => halts word)
      (fun word length => length ▸ bounded word) L language
  · intro n
    apply Machine.SpaceBound.mono (machine D)
      (machine_spaceBound D first least deterministic n (space n) (fun word _ => halts word)
        (fun word length => length ▸ bounded word))
    have majorant := PolynomialBound.eval_le_ofPolynomial polynomial n
    simpa [generatorSpace, polynomial, radius, PolynomialBound.asPolynomial_eval,
      Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc] using majorant

/-- Appendix A.17, reverse direction, for every finite alphabet. The empty
alphabet has only the empty word and is handled by the existing elementary
generators, which use one work cell. -/
theorem pspace_subset_pspaceg : PSPACE α ⊆ PSPACEG α := by
  classical
  by_cases inhabited : Nonempty α
  · letI := inhabited
    exact pspace_subset_pspaceg_of_nonempty
  · letI : IsEmpty α := ⟨fun a => inhabited ⟨a⟩⟩
    intro L _
    have words : ∀ word : List α, word = [] := by
      intro word
      cases word with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    by_cases containsEmpty : [] ∈ L
    · have same : L = {[]} := by
        ext word
        rw [words word]
        simp [containsEmpty]
      rw [same]
      exact empty_word_language_in_pspaceg
    · have same : L = ∅ := by
        ext word
        rw [words word]
        simp [containsEmpty]
      rw [same]
      exact empty_language_in_pspaceg

end
end ComplexityOfGenerators
