import ComplexityOfGenerators.Simulation.IndexedGeneratorRecognizer
import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Simulation.IndexLocality

/-! The upper containment in Theorem 5.1. Its NP argument uses exactly the
the paper’s global word-length condition. The historical layer-fast
criterion is retained separately, with explicit producing-index coverage.
Neither first moments nor an expected-time simulator are used for this part. -/

namespace ComplexityOfGenerators

open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

theorem indexedGeneratorRecognizer_sound (G : UniformGenerators α) (w : List α) (bits : BitString)
    (accepted : (indexedGeneratorRecognizer G.machine).Accepts (decisionData w) bits) :
    w ∈ G.language := by
  obtain ⟨out, acceptedTime, accepted⟩ := accepted
  rcases indexChoice_cases bits with ⟨i, rfl⟩ | ⟨i, tail, rfl⟩
  · have exhausted := guessedIndex_exhausted G.machine w i
    rw [← (guessedIndexLoader G.machine).runFrom_initial] at exhausted
    have lifted := sequence_left_exhausted (guessedIndexLoader G.machine)
      (generatorMatcherRoutine G.machine) (decisionData w) (List.replicate i true)
      (guessedIndexLoader G.machine).initialConfiguration [] (2 * i + 1) exhausted
    have initial : sequenceLeftConfiguration (guessedIndexLoader G.machine)
        (generatorMatcherRoutine G.machine) (guessedIndexLoader G.machine).initialConfiguration [] =
        (indexedGeneratorRecognizer G.machine).initialConfiguration := rfl
    rw [initial] at lifted
    change (indexedGeneratorRecognizer G.machine).runFrom (decisionData w) (List.replicate i true)
      (indexedGeneratorRecognizer G.machine).initialConfiguration (2 * i + 1) = .halted .exhausted at lifted
    rw [Machine.runFrom_initial] at lifted
    have same := (indexedGeneratorRecognizer G.machine).halted_outcome_unique _ _ _ _ _ _ accepted lifted
    cases same
  · obtain ⟨t, result, execution⟩ := (G.isGenerator i).1.1 tail
    obtain ⟨ticks, _, simulated⟩ := indexedGeneratorRecognizer_run G.machine w i t tail result execution
    have same := (indexedGeneratorRecognizer G.machine).halted_outcome_unique _ _ _ _ _ _ accepted simulated
    cases result with
    | rejected => simp [matcherOutcome] at same
    | exhausted => simp [matcherOutcome] at same
    | accepted v =>
      have word : v = w := by
        by_contra different
        simp [matcherOutcome, different] at same
      subst v
      exact ⟨i, tail ++ [false], by simp,
        G.machine.produces_append (generatorData i) tail [false] w ⟨t, execution⟩⟩

def indexedRecognizerTime (p q : PolynomialBound) : PolynomialBound :=
  let j := q.asPolynomial
  let t := p.asPolynomial.comp j
  PolynomialBound.ofPolynomial (3 * j + 4 + (t + 1) * (2 * (j + 1 + t) + 2 * j + 8))

theorem indexedRecognizerTime_bound (p q : PolynomialBound) (n i : ℕ) (index : i ≤ q n) :
    3 * i + 4 + (p i + 1) * (2 * (i + 1 + p i) + 2 * i + 8) ≤ indexedRecognizerTime p q n := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_ofNat, Polynomial.eval_one, PolynomialBound.asPolynomial_eval]
  have time := p.monotone index
  gcongr

/-- A support criterion for the stronger layer-fast variant. Neither first
moments nor an infinitude hypothesis is needed for this sufficient condition. -/
theorem uniform_mem_np_of_index_coverage (G : UniformGenerators α)
    (coverage : G.PolynomialIndexCoverage)
    (short : ∃ p : PolynomialBound, ∀ i w, w ∈ G.layer i →
      ∃ bits : BitString, bits ≠ [] ∧
        G.machine.run (generatorData i) bits (p i) = .halted (.accepted w)) :
    G.language ∈ NP α := by
  obtain ⟨q, coverage⟩ := coverage
  obtain ⟨p, short⟩ := short
  apply np_of_bounded_acceptance G.language (indexedGeneratorRecognizer G.machine) (indexedRecognizerTime p q)
  · exact indexedGeneratorRecognizer_sound G
  · intro w member
    obtain ⟨i, index, produced⟩ := coverage w member
    obtain ⟨bits, _, execution⟩ := short i w produced
    obtain ⟨ticks, bound, run⟩ := indexedGeneratorRecognizer_run G.machine w i (p i) bits (.accepted w) execution
    have limit := bound.trans (indexedRecognizerTime_bound p q w.length i index)
    refine ⟨indexChoice i ++ bits, [], ?_⟩
    have padded := (indexedGeneratorRecognizer G.machine).run_halted_add (decisionData w)
      (indexChoice i ++ bits) ticks (.accepted []) (by simpa [matcherOutcome] using run)
      (indexedRecognizerTime p q w.length - ticks)
    simpa only [Nat.add_sub_of_le limit] using padded

/-- The source runtime and guessed index are bounded independently by the
input word length. This is the form needed by the current paper's ELEPG. -/
def indexedWordRecognizerTime (p q : PolynomialBound) : PolynomialBound :=
  let j := q.asPolynomial
  let t := p.asPolynomial
  PolynomialBound.ofPolynomial (3*j+4+(t+1)*(2*(j+1+t)+2*j+8))

theorem indexedWordRecognizerTime_bound (p q : PolynomialBound) (n i t : ℕ)
    (index : i≤q n) (runtime : t≤p n) :
    3*i+4+(t+1)*(2*(i+1+t)+2*i+8) ≤ indexedWordRecognizerTime p q n := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,
    PolynomialBound.asPolynomial_eval]
  gcongr

/-- A genuine family with globally short, bounded-index output witnesses is
recognised by an actual native nondeterministic polynomial machine. -/
theorem uniform_mem_np_of_bounded_index_word_time (G : UniformGenerators α)
    (p q : PolynomialBound)
    (paths : ∀ word∈G.language,∃ i,i≤q word.length ∧ ∃ bits : BitString,
      G.machine.run (generatorData i) bits (p word.length)=.halted (.accepted word)) :
    G.language∈NP α := by
  apply np_of_bounded_acceptance G.language (indexedGeneratorRecognizer G.machine) (indexedWordRecognizerTime p q)
  · exact indexedGeneratorRecognizer_sound G
  · intro word member
    obtain ⟨i,index,bits,accepted⟩ := paths word member
    obtain ⟨ticks,cost,run⟩ := indexedGeneratorRecognizer_run G.machine word i (p word.length) bits (.accepted word) accepted
    have limit := cost.trans (indexedWordRecognizerTime_bound p q word.length i (p word.length) index le_rfl)
    refine ⟨indexChoice i++bits,[],?_⟩
    have padded := (indexedGeneratorRecognizer G.machine).run_halted_add (decisionData word)
      (indexChoice i++bits) ticks (.accepted []) (by simpa [matcherOutcome] using run)
      (indexedWordRecognizerTime p q word.length-ticks)
    simpa only [Nat.add_sub_of_le limit] using padded

namespace UniformGenerators.GlobalWordPolynomialTime

/-- Unary-index locality bounds the producing index without strengthening the
paper's fast-path condition or assuming fast paths for other layer members. -/
theorem bounded_paths {G : UniformGenerators α} (fast : G.GlobalWordPolynomialTime) :
    ∃ p : PolynomialBound,∀ word∈G.language,∃ i,i≤p word.length+1 ∧ ∃ bits : BitString,
      bits≠[] ∧ G.machine.run (generatorData i) bits (p word.length)=.halted (.accepted word) := by
  obtain ⟨p,fast⟩ := fast
  refine ⟨p,fun word member=>?_⟩
  obtain ⟨i,bits,nonempty,run⟩ := fast word member
  obtain ⟨j,index,accepted⟩ := G.machine.exists_bounded_index_of_accepted i (p word.length) bits word run
  exact ⟨j,index,bits,nonempty,accepted⟩

end UniformGenerators.GlobalWordPolynomialTime

def globalWordIndexBound (p : PolynomialBound) : PolynomialBound := p.add ⟨1,0,by decide⟩

theorem globalWordIndexBound_lower (p : PolynomialBound) (n : ℕ) : p n+1≤globalWordIndexBound p n := by
  simpa only [globalWordIndexBound,PolynomialBound.eval,pow_zero,Nat.mul_one] using
    p.add_le (⟨1,0,by decide⟩ : PolynomialBound) n

/-- The early-index consequence mentioned immediately after the ELEPG definition in
current PLDI27. It is derived from global short paths, not an extra premise. -/
theorem UniformGenerators.GlobalWordPolynomialTime.indexCoverage {G : UniformGenerators α}
    (fast : G.GlobalWordPolynomialTime) : G.PolynomialIndexCoverage := by
  obtain ⟨p,paths⟩ := fast.bounded_paths
  refine ⟨globalWordIndexBound p,fun word member=>?_⟩
  obtain ⟨i,index,bits,nonempty,run⟩ := paths word member
  exact ⟨i,index.trans (globalWordIndexBound_lower p word.length),bits,nonempty,p word.length,run⟩

/-- NP containment uses only the actual family's global word-length paths;
expected moments are not needed in the verifier construction. -/
theorem uniform_mem_np_of_global_word_time (G : UniformGenerators α) (fast : G.GlobalWordPolynomialTime) :
    G.language∈NP α := by
  obtain ⟨p,paths⟩ := fast.bounded_paths
  apply uniform_mem_np_of_bounded_index_word_time G p (globalWordIndexBound p)
  intro word member
  obtain ⟨i,index,bits,_,run⟩ := paths word member
  exact ⟨i,index.trans (globalWordIndexBound_lower p word.length),bits,run⟩

/-- The current paper's ELEPG upper inclusion, with its global word-time
condition rather than the stronger historical per-layer condition. -/
theorem elepg_subset_np : ELEPG α ⊆ NP α := by
  rintro L ⟨_,G,language,_,_,_,fast⟩
  rw [←language]
  exact uniform_mem_np_of_global_word_time G fast

theorem layerFastELEPG_subset_np : LayerFastELEPG α ⊆ NP α := by
  rintro L ⟨_, G, language, _, _, ⟨p, _, short⟩, coverage⟩
  rw [← language]
  exact uniform_mem_np_of_index_coverage G coverage ⟨p, short⟩

end
end ComplexityOfGenerators
