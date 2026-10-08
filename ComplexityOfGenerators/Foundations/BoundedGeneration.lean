import ComplexityOfGenerators.ComplexityClasses
import ComplexityOfGenerators.Foundations.RandomTape
import ComplexityOfGenerators.Foundations.ResourceBounds

/-!
# Finite witnesses for time-bounded generation

The Remark 1 convention bounds trials on short tapes, not arbitrary tapes.
To use it in a recognition proof, every generated word must still have a
full-budget seed witness. This is proved here from read-once tape extension and
unique halting outcomes, rather than assumed as an additional generation axiom.
-/

namespace ComplexityOfGenerators

/-- P is contained in NP directly in the local finite-control model. This proof
needs no unproved comparison with Complexitylib's classes. -/
theorem p_subset_np {α : Type} [Fintype α] : P α ⊆ NP α := by
  rintro L ⟨M, p, deterministic, time, recognizes⟩
  refine ⟨M, p, time, fun w => ?_⟩
  simp_rw [M.deterministic_accepts deterministic (decisionData w) _ []]
  simpa using recognizes w

namespace Machine

variable {I A O : Type} (M : Machine I A O)

theorem produces_unique (data : InputData I A) (bits : BitString) (v w : List O)
    (hv : M.Produces data bits v) (hw : M.Produces data bits w) : v = w := by
  obtain ⟨s, hs⟩ := hv
  obtain ⟨t, ht⟩ := hw
  exact Outcome.accepted.inj (M.halted_outcome_unique data bits s t _ _ hs ht)

theorem produces_at_bound (data : InputData I A) (bits : BitString)
    (t : ℕ) (w : List O) (halts : M.HaltsWithin data bits t)
    (produces : M.Produces data bits w) : M.run data bits t = .halted (.accepted w) := by
  obtain ⟨result, result_eq⟩ := halts
  obtain ⟨s, accepts⟩ := produces
  have same := M.halted_outcome_unique data bits t s result (.accepted w) result_eq accepts
  simpa [same] using result_eq

/-- Every word, even one initially witnessed by a tape longer than the budget,
has a full-budget witness. No lower bound on the word's probability is needed. -/
theorem generatedLanguage_iff_budget_seed (data : InputData I A) (seed t : ℕ)
    (positive : 0 < seed) (bound : M.GeneratorTimeBound data seed t) (w : List O) :
    w ∈ M.generatedLanguage data ↔
      ∃ bits : BitString, bits.length = seed ∧ M.run data bits t = .halted (.accepted w) := by
  constructor
  · intro member
    obtain ⟨bits, nonempty, produces⟩ := member
    by_cases short : bits.length ≤ seed
    · let full := bits ++ List.replicate (seed - bits.length) false
      have length : full.length = seed := by simp [full]; omega
      refine ⟨full, length, ?_⟩
      exact M.produces_at_bound data full t w (bound.1 full length.le)
        (M.produces_append data bits _ w produces)
    · let full := bits.take seed
      have length : full.length = seed := by simp [full, List.length_take]; omega
      have accepts : M.Accepts data full :=
        (bound.2 full length).2 ⟨w, bits, nonempty, produces⟩
      obtain ⟨v, hv⟩ := accepts
      have same : v = w := M.produces_unique data bits v w
        (M.produces_prefix (List.take_prefix seed bits) hv) produces
      subst v
      exact ⟨full, length, M.produces_at_bound data full t w (bound.1 full length.le) hv⟩
  · rintro ⟨bits, length, produces⟩
    refine ⟨bits, ?_, t, produces⟩
    intro empty
    simp [empty] at length
    omega

end Machine

theorem GeneratorFamily.layer_eq_lengthSlice {α : Type} [Fintype α]
    (G : GeneratorFamily α) (n : ℕ) :
    G.toUniformGenerators.layer n = lengthSlice G.toUniformGenerators.language n := by
  ext w
  constructor
  · intro member
    exact ⟨⟨n, member⟩, G.outputLength n w member⟩
  · rintro ⟨⟨m, member⟩, length⟩
    have index := G.outputLength m w member
    have same : m = n := index.symm.trans length
    simpa [same] using member

/-- The precise witness predicate used by the PG-to-NP simulation. It has one
uniform machine, a polynomial seed length and a polynomial simulation clock. -/
theorem pg_has_bounded_witnesses {α : Type} [Fintype α] {L : Language α}
    (member : L ∈ PG α) :
    ∃ G : GeneratorFamily α, ∃ seed time : PolynomialBound,
      ∀ w, w ∈ L ↔ ∃ bits : BitString,
        bits.length = seed w.length ∧
        G.machine.run (generatorData w.length) bits (time w.length) = .halted (.accepted w) := by
  obtain ⟨G, language, seed, time, bound⟩ := member
  refine ⟨G, seed, time, fun w => ?_⟩
  have layer := G.layer_eq_lengthSlice w.length
  rw [language] at layer
  have word : w ∈ L ↔ w ∈ G.toUniformGenerators.layer w.length := by
    rw [layer]
    simp [lengthSlice]
  rw [word]
  exact G.machine.generatedLanguage_iff_budget_seed (generatorData w.length)
    (seed w.length) (time w.length) (seed.positive w.length) (bound w.length) w

end ComplexityOfGenerators
