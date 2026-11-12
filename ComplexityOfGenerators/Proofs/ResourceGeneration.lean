import ComplexityOfGenerators.Proofs.NonemptyTrialBounds
import ComplexityOfGenerators.Proofs.GeneratorSupport
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition
import ComplexityOfGenerators.Simulation.GeneratorRecognizerCorrectness
import ComplexityOfGenerators.Foundations.StreamPrefixExecution

/-!
# Accepting-time bounds and reusable native output comparison

The current paper bounds accepting runs only.  This module records that
condition independently of the older short-seed trial contract, proves the
one-way implication from that contract, and supplies a single output-matcher
correctness result shared by exact, cumulative, and expected-time generation.
-/

namespace ComplexityOfGenerators

open scoped ENNReal

namespace Machine

/-- Every accepting run has reached its accepted outcome by this deadline.
Runs that never accept impose no obligation.  Stability after halting makes
this equivalent to a bound on the first acceptance time. -/
def AcceptingTimeBound {I A O : Type} (M : Machine I A O)
    (data : InputData I A) (time : ℕ) : Prop :=
  ∀ bits word, M.Produces data bits word →
    M.run data bits time = .halted (.accepted word)

theorem TimeBound.acceptingTimeBound {I A O : Type} {M : Machine I A O}
    {data : InputData I A} {time : ℕ} (bound : M.TimeBound data time) :
    M.AcceptingTimeBound data time :=
  fun bits word produced => M.produces_at_bound data bits time word (bound bits) produced

/-- The current accepting-time convention suffices for the full-prefix test.
The native evaluator can inspect the initial cell before a transition, hence
the safe prefix length is `time + 1`.  No short-tape halting-time condition or
full-trial acceptance equivalence is assumed. -/
theorem accepts_full_prefix_of_acceptingTimeBound {I A O : Type}
    (M : Machine I A O) (data : InputData I A) (time : ℕ)
    (generator : M.IsGenerator data) (bound : M.AcceptingTimeBound data time)
    (bits : BitString) (length : bits.length = time + 1) :
    M.Accepts data bits ↔ (M.generatedLanguage data).Nonempty := by
  classical
  constructor
  · intro accepted
    exact (M.generatedLanguage_nonempty_iff_accepts data).mpr ⟨bits, accepted⟩
  · intro nonempty
    by_contra notAccepted
    have subset : cylinder bits ⊆ (M.acceptedStreams data)ᶜ := by
      intro stream inCylinder accepted
      obtain ⟨seed, inSeed, word, ticks, execution⟩ := accepted
      have atBound := bound seed word ⟨ticks, execution⟩
      have onPrefix := M.run_on_streamPrefix_of_accepting_prefix data inSeed atBound
      have same : streamPrefix stream (time + 1) = bits := by
        apply List.ext_getElem
        · simpa using length.symm
        · intro j left right
          have letter := inCylinder ⟨j, right⟩
          change stream j = bits[j] at letter
          simpa only [streamPrefix, List.getElem_ofFn] using letter
      rw [same] at onPrefix
      exact notAccepted ⟨word, time, onPrefix⟩
    have probability : fairCoinMeasure (M.acceptedStreams data) = 1 :=
      (M.generator_probability_one_iff_nonempty data generator).mpr nonempty
    have null : fairCoinMeasure (M.acceptedStreams data)ᶜ = 0 := by
      rw [MeasureTheory.measure_compl (M.measurableSet_acceptedStreams data)
          (by simp [probability]),
        MeasureTheory.measure_univ, probability]
      simp
    have positive : 0 < fairCoinMeasure (cylinder bits) := by
      rw [fairCoinMeasure_cylinder]
      exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0))
    have impossible : fairCoinMeasure (cylinder bits) ≤ 0 :=
      (MeasureTheory.measure_mono subset).trans_eq null
    exact (not_lt_of_ge impossible) positive

end Machine

namespace UniformGenerators

/-- Polynomial accepting-time bounds, with no bound on rejecting empty slices. -/
def AcceptingPolynomialTime {α : Type} [Fintype α] (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound, ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n)

/-- The older separate-budget convention implies the accepting-time condition.
The converse is not asserted by this lemma. -/
theorem PolynomialTime.acceptingPolynomialTime {α : Type} [Fintype α]
    {G : UniformGenerators α} (bounded : G.PolynomialTime) : G.AcceptingPolynomialTime := by
  obtain ⟨seed, time, bound⟩ := bounded
  refine ⟨time, fun n bits word produced => ?_⟩
  have nonempty : (G.machine.generatedLanguage (generatorData n)).Nonempty :=
    ⟨word, bits ++ [false], by simp, G.machine.produces_append _ bits [false] word produced⟩
  have total := G.machine.generatorTimeBound_timeBound_of_nonempty _ _ _ (bound n) nonempty
  exact G.machine.produces_at_bound _ bits _ word (total bits) produced

end UniformGenerators

noncomputable section

variable {α : Type} [Fintype α]

/-- The native matcher recognises the source layer indexed by input length.
No exact-output-length condition is used here. -/
theorem generatorRecognizer_accepts_iff_layer (G : UniformGenerators α) (w : Word α) :
    (∃ bits, (Simulation.generatorRecognizer G.machine).Accepts (decisionData w) bits) ↔
      w ∈ G.layer w.length := by
  constructor
  · rintro ⟨bits, out, acceptedTime, accepts⟩
    obtain ⟨time, result, halted⟩ := (G.isGenerator w.length).1.1 bits
    have simulated := Simulation.generatorRecognizer_run G.machine w bits time result halted
    have same := (Simulation.generatorRecognizer G.machine).halted_outcome_unique
      (decisionData w) bits acceptedTime _ (.accepted out)
      (Simulation.matcherOutcome w result) accepts simulated
    cases result with
    | rejected => simp [Simulation.matcherOutcome] at same
    | exhausted => simp [Simulation.matcherOutcome] at same
    | accepted v =>
        have word : v = w := by
          by_contra different
          simp [Simulation.matcherOutcome, different] at same
        subst v
        exact ⟨bits ++ [false], by simp,
          G.machine.produces_append _ bits [false] w ⟨time, halted⟩⟩
  · rintro ⟨bits, _, time, accepted⟩
    refine ⟨bits, [], 6 * w.length + 13 +
      (time + 1) * (2 * time + 2 * w.length + 8), ?_⟩
    simpa only [Simulation.matcherOutcome, ↓reduceIte] using
      Simulation.generatorRecognizer_run G.machine w bits time (.accepted w) accepted

/-- A polynomially short generating run for each word in its input-length
layer suffices for NP.  The source's other runs may take arbitrarily long. -/
theorem mem_np_of_polynomial_layer_witnesses (L : Language α) (G : UniformGenerators α)
    (coverage : ∀ w, w ∈ G.layer w.length ↔ w ∈ L)
    (p : PolynomialBound)
    (witnesses : ∀ w, w ∈ G.layer w.length → ∃ bits,
      G.machine.run (generatorData w.length) bits (p w.length) = .halted (.accepted w)) :
    L ∈ NP α := by
  apply np_of_bounded_acceptance L (Simulation.generatorRecognizer G.machine)
    (Simulation.generatorRecognizerTime p)
  · intro w bits accepted
    exact (coverage w).mp ((generatorRecognizer_accepts_iff_layer G w).mp ⟨bits, accepted⟩)
  · intro w member
    obtain ⟨bits, produced⟩ := witnesses w ((coverage w).mpr member)
    exact ⟨bits, [], Simulation.generatorRecognizer_accepts_at_bound G.machine p w bits
      produced⟩

/-- One uniform generator with the right length-indexed membership predicate
and polynomial accepting runtime supplies an actual polynomial nondeterministic
decider.  Neither exact lengths nor cumulative slices are assumed here. -/
theorem mem_np_of_polynomial_layer_generation (L : Language α) (G : UniformGenerators α)
    (coverage : ∀ w, w ∈ G.layer w.length ↔ w ∈ L)
    (bounded : G.AcceptingPolynomialTime) : L ∈ NP α := by
  obtain ⟨p, bound⟩ := bounded
  apply mem_np_of_polynomial_layer_witnesses L G coverage p
  intro word member
  obtain ⟨bits, _, produced⟩ := member
  exact ⟨bits, bound word.length bits word produced⟩

end
end ComplexityOfGenerators
