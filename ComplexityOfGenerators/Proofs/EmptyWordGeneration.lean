import ComplexityOfGenerators.Proofs.ElementaryGenerators
import ComplexityOfGenerators.Certificates

/-!
# The empty word is polynomially generable

The size-zero slice accepts immediately and every positive-size slice consumes
its random tape to exhaustion. This is a native uniform generator, including
the separate seed/time budgets of Remark 1. It also supplies a counterexample
to the literal empty-word exclusion in the paper's certificate definitions.
-/

namespace ComplexityOfGenerators

variable (α : Type) [Fintype α]

def emptyWordGenerator : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 1
  symbols := 0
  initial := 0
  transition := fun _ _ _ index _ => if index.isNone then .accept else .readRandom 0 0

def emptyWordConfiguration (t : ℕ) : Configuration (emptyWordGenerator α) :=
  {(emptyWordGenerator α).initialConfiguration with randomHead := t}

theorem emptyWordGenerator_run_zero (bits : BitString) (t : ℕ) :
    (emptyWordGenerator α).run (generatorData 0) bits t = .halted (.accepted []) := by
  have initial : (emptyWordGenerator α).run (generatorData 0) bits 0 = .halted (.accepted []) := rfl
  simpa using (emptyWordGenerator α).run_halted_add _ bits 0 _ initial t

theorem emptyWordGenerator_run_positive (n : ℕ) (positive : 0 < n) (bits : BitString) (t : ℕ) :
    (emptyWordGenerator α).run (generatorData n) bits t =
      if t < bits.length then .running (emptyWordConfiguration α t) else .halted .exhausted := by
  induction t with
  | zero =>
      simp [Machine.run, Machine.observe, emptyWordGenerator, Machine.initialConfiguration,
        generatorData, positive, emptyWordConfiguration]
      rfl
  | succ t ih =>
      rw [Machine.run, ih]
      by_cases available : t < bits.length
      · rw [ite_eq_left available]
        have lookup := List.getElem?_eq_getElem available
        simp only [Machine.next, emptyWordGenerator, emptyWordConfiguration,
          Machine.initialConfiguration, generatorData, positive, ↓reduceIte, Option.isNone_some,
          Bool.false_eq_true, lookup]
        cases bits[t] <;> simp [Machine.observe, positive]
      · simp [available, show ¬t + 1 < bits.length by omega]

theorem emptyWordGenerator_no_accept_positive (n : ℕ) (positive : 0 < n) (bits : BitString) :
    ¬ (emptyWordGenerator α).Accepts (generatorData n) bits := by
  rintro ⟨word, t, accepted⟩
  rw [emptyWordGenerator_run_positive α n positive] at accepted
  split_ifs at accepted
  cases accepted

theorem emptyWordGenerator_language (n : ℕ) :
    (emptyWordGenerator α).generatedLanguage (generatorData n) =
      if n = 0 then {[]} else ∅ := by
  by_cases zero : n = 0
  · subst n
    ext word
    simp only [↓reduceIte, Set.mem_singleton_iff]
    constructor
    · rintro ⟨bits, _, t, run⟩
      simpa [emptyWordGenerator_run_zero] using run.symm
    · rintro rfl
      exact ⟨[false], by simp, 0, emptyWordGenerator_run_zero α [false] 0⟩
  · rw [ite_eq_right zero]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro word ⟨bits, _, produced⟩
    exact emptyWordGenerator_no_accept_positive α n (by omega) bits ⟨word, produced⟩

theorem emptyWordGenerator_isGenerator (n : ℕ) :
    (emptyWordGenerator α).IsGenerator (generatorData n) := by
  by_cases zero : n = 0
  · subst n
    have allStreams : (emptyWordGenerator α).acceptedStreams (generatorData 0) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro stream
      exact ⟨[], by simp [cylinder], [], 0, emptyWordGenerator_run_zero α [] 0⟩
    refine ⟨⟨fun bits => ⟨0, .accepted [], emptyWordGenerator_run_zero α bits 0⟩, ?_⟩, Or.inl ?_⟩
    · intro bits t
      simp [emptyWordGenerator_run_zero]
    · rw [allStreams]
      exact MeasureTheory.measure_univ
  · have positive : 0 < n := by omega
    have noStreams : (emptyWordGenerator α).acceptedStreams (generatorData n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro stream ⟨bits, _, accepted⟩
      exact emptyWordGenerator_no_accept_positive α n positive bits accepted
    refine ⟨⟨?_, ?_⟩, Or.inr ?_⟩
    · intro bits
      exact ⟨bits.length, .exhausted, by simp [emptyWordGenerator_run_positive α n positive]⟩
    · intro bits t
      rw [emptyWordGenerator_run_positive α n positive]
      split_ifs <;> simp
    · simp [noStreams]

theorem emptyWordGenerator_trial (n : ℕ) :
    (emptyWordGenerator α).GeneratorTimeBound (generatorData n) 1 1 := by
  by_cases zero : n = 0
  · subst n
    refine ⟨fun bits _ => ⟨.accepted [], emptyWordGenerator_run_zero α bits 1⟩, ?_⟩
    intro bits length
    constructor
    · intro _
      simp [emptyWordGenerator_language]
    · intro _
      exact ⟨[], 0, emptyWordGenerator_run_zero α bits 0⟩
  · have positive : 0 < n := by omega
    refine ⟨?_, ?_⟩
    · intro bits length
      exact ⟨.exhausted, by simp [emptyWordGenerator_run_positive α n positive, show ¬1 < bits.length by omega]⟩
    · intro bits length
      simp [emptyWordGenerator_language, zero, emptyWordGenerator_no_accept_positive α n positive]

/-- The empty word is allowed by the original definition of `PG`, even over
an empty alphabet. Both uniform polynomial budgets are the constant one. -/
theorem empty_word_language_in_pg : ({[]} : Language α) ∈ PG α := by
  let G : GeneratorFamily α := {
    machine := emptyWordGenerator α
    isGenerator := emptyWordGenerator_isGenerator α
    outputLength := by
      intro n word member
      change word ∈ (emptyWordGenerator α).generatedLanguage (generatorData n) at member
      rw [emptyWordGenerator_language] at member
      split_ifs at member with zero
      · have empty : word = [] := member
        simp [empty, zero]
      · exact False.elim member }
  refine ⟨G, ?_, ⟨1, 0, by decide⟩, ⟨1, 0, by decide⟩, ?_⟩
  · ext word
    change (∃ n, word ∈ (emptyWordGenerator α).generatedLanguage (generatorData n)) ↔ word = []
    simp [emptyWordGenerator_language]
  · intro n
    simpa [PolynomialBound.eval] using emptyWordGenerator_trial α n

omit [Fintype α] in
/-- The original `Σ⁺` restriction prevents even certificate coverage at `L = {ε}`.
This is about the historical condition, not the corrected certificate scheme,
and is proved independently of the main theorem. -/
theorem empty_word_has_no_literal_certificate_coverage :
    ¬ ∃ V : PolynomialVerifier ({[]} : Language α), LiteralCertificateCoverage V := by
  rintro ⟨V, coverage⟩
  exact literal_certificate_coverage_excludes_empty_word V coverage (Set.mem_singleton _)

theorem literal_certificate_coverage_characterization_false :
    ¬ (∀ L : Language α, L ∈ PG α ↔ ∃ V : PolynomialVerifier L, LiteralCertificateCoverage V) := by
  intro characterization
  exact empty_word_has_no_literal_certificate_coverage α
    ((characterization {[]}).mp (empty_word_language_in_pg α))

end ComplexityOfGenerators
