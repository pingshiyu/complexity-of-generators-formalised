import ComplexityOfGenerators.Proofs.UpToGeneration
import ComplexityOfGenerators.Proofs.UpToElementaryGenerators
import ComplexityOfGenerators.Simulation.FixedFallbackSemantics
import ComplexityOfGenerators.Simulation.FiniteUpToWordSampler

/-! The polynomial-time converse for cumulative generation over finite alphabets.  A shortest
word of a nonempty language is fixed in the finite control.  The actual native
machine samples a word of length at most the index, simulates a bounded NP
branch, and emits the fixed word if that branch rejects. -/

namespace ComplexityOfGenerators

open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UpToPolynomialGeneration

variable (α : Type) [Fintype α] [Nonempty α]

def ticksPolynomial (p : PolynomialBound) (k : ℕ) : Polynomial ℕ :=
  Polynomial.C (10 + 5 * (Fintype.card α + 2)) * Polynomial.X + 5 * p.asPolynomial + Polynomial.C (3 * k + 30)

def timePolynomial (p : PolynomialBound) (k : ℕ) : Polynomial ℕ :=
  let ticks := ticksPolynomial α p k
  1 + (ticks + 1) * (2 * ticks + 4)

def timeBound (p : PolynomialBound) (k : ℕ) : PolynomialBound :=
  PolynomialBound.ofPolynomial (timePolynomial α p k)

omit [Nonempty α] in
theorem time_bound (p : PolynomialBound) (k n : ℕ) :
    let ticks := (10 + 5 * (Fintype.card α + 2)) * n + 5 * p n + 3 * k + 30
    1 + (ticks + 1) * (2 * ticks + 4) ≤ timeBound α p k n := by
  have bound := PolynomialBound.eval_le_ofPolynomial (timePolynomial α p k) n
  change (timePolynomial α p k).eval n ≤ timeBound α p k n at bound
  simp only [timePolynomial, ticksPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one,
    PolynomialBound.asPolynomial_eval] at bound
  simpa only [Nat.add_assoc] using bound

variable (L : Language α) (M : Machine α Bool Unit) (p : PolynomialBound)
    (time : ∀ word, M.TimeBound (decisionData word) (p word.length))
    (language : ∀ word, (∃ bits, M.Accepts (decisionData word) bits) ↔ word ∈ L)
    (fallback : List α) (member : fallback ∈ L)
    (shortest : ∀ word ∈ L, fallback.length ≤ word.length)

include time

theorem live_execution (n : ℕ) (bits : BitString) (live : fallback.length ≤ n) :
    ∃ ticks result, ticks ≤ (10 + 5 * (Fintype.card α + 2)) * n + 5 * p n + 3 * fallback.length + 30 ∧
      (fixedFallbackBank (finiteUpToWordSampler α) M fallback).Executes (generatorData n) bits
        (fixedFallbackBank (finiteUpToWordSampler α) M fallback).initialConfiguration ticks result ∧
      (match result with
        | .accepted word => (word.length ≤ n ∧ (∃ choices, M.Accepts (decisionData word) choices)) ∨ word = fallback
        | .rejected => False
        | .exhausted => bits.length ≤ (2 + 4 * (Fintype.card α + 2)) * n + p n + 3) := by
  obtain ⟨ticks, result, cost, execution, related⟩ := fixedFallback_executes_live (finiteUpToWordSampler α) M fallback n
    ((Fintype.card α + 2) * n) (p n) bits live (finiteUpToWordSampler_run α n)
    (fun word length bits => M.haltsWithin_mono _ bits (p.monotone length) (time word bits))
  refine ⟨ticks, result, ?_, execution, ?_⟩
  · have equal : (10 + 5 * (Fintype.card α + 2)) * n + 5 * p n + 3 * fallback.length + 30 =
        10 * n + 5 * ((Fintype.card α + 2) * n) + 5 * p n + 3 * fallback.length + 30 := by ring
    rw [equal]
    exact cost
  · cases result with
    | accepted word => exact related
    | rejected => exact related
    | exhausted =>
        have equal : (2 + 4 * (Fintype.card α + 2)) * n + p n + 3 =
            2 * n + 4 * ((Fintype.card α + 2) * n) + p n + 3 := by ring
        rw [equal]
        exact related

theorem live_timeBound (n : ℕ) (live : fallback.length ≤ n) :
    (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).TimeBound (generatorData n) (timeBound α p fallback.length n) := by
  intro bits
  obtain ⟨ticks, result, cost, execution, _⟩ := live_execution α M p time fallback n bits live
  obtain ⟨nativeTicks, nativeCost, native⟩ := TransducerBank.bank_run
    (fixedFallbackBank (finiteUpToWordSampler α) M fallback) _ bits ticks result execution
  have upper : nativeTicks ≤ timeBound α p fallback.length n := by
    apply nativeCost.trans
    apply le_trans _ (time_bound α p fallback.length n)
    gcongr
  exact (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).haltsWithin_mono _ bits upper ⟨result, native⟩

omit time in
theorem below_execution (n : ℕ) (bits : BitString) (below : n < fallback.length) :
    ∃ ticks, (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).run (generatorData n) bits ticks = .halted .exhausted := by
  obtain ⟨ticks, _, execution⟩ := fixedFallback_executes_below (finiteUpToWordSampler α) M fallback n bits below
  obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run
    (fixedFallbackBank (finiteUpToWordSampler α) M fallback) _ bits ticks .exhausted execution
  exact ⟨nativeTicks, native⟩

include language member shortest

theorem generatedLanguage (n : ℕ) :
    (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).generatedLanguage (generatorData n) = upToSlice L n := by
  exact fixedFallback_support (finiteUpToWordSampler α) M fallback L n ((Fintype.card α + 2) * n) (p n)
    (finiteUpToWordSampler_run α n)
    (fun word length => by rw [finiteUpToWordSampler_language]; exact length)
    (fun word length bits => M.haltsWithin_mono _ bits (p.monotone length) (time word bits))
    language member shortest

theorem isGenerator (n : ℕ) :
    (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).IsGenerator (generatorData n) := by
  exact fixedFallback_isGenerator (finiteUpToWordSampler α) M fallback L n ((Fintype.card α + 2) * n) (p n)
    (finiteUpToWordSampler_run α n)
    (fun word length => by rw [finiteUpToWordSampler_language]; exact length)
    (fun word length bits => M.haltsWithin_mono _ bits (p.monotone length) (time word bits))
    language member shortest

omit language member shortest in
theorem acceptingTimeBound (n : ℕ) :
    (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).AcceptingTimeBound (generatorData n) (timeBound α p fallback.length n) := by
  by_cases live : fallback.length ≤ n
  · exact (live_timeBound α M p time fallback n live).acceptingTimeBound
  · intro bits word ⟨ticks, accepted⟩
    obtain ⟨otherTicks, exhausted⟩ := below_execution α M fallback n bits (by omega)
    have same := (fixedFallbackGenerator (finiteUpToWordSampler α) M fallback).halted_outcome_unique _ bits ticks otherTicks _ _ accepted exhausted
    cases same

theorem mem_pgUpTo : L ∈ PGUpTo α := by
  refine ⟨{ machine := fixedFallbackGenerator (finiteUpToWordSampler α) M fallback
            isGenerator := isGenerator α L M p time language fallback member shortest
            layers := generatedLanguage α L M p time language fallback member shortest },
    timeBound α p fallback.length, ?_⟩
  exact acceptingTimeBound α M p time fallback

end UpToPolynomialGeneration

theorem empty_mem_pgUpTo {α : Type} [Fintype α] : (∅ : Language α) ∈ PGUpTo α := by
  refine ⟨emptyUpToFamily α, ⟨1, 0, by decide⟩, ?_⟩
  intro n bits word ⟨ticks, accepted⟩
  change (emptyGenerator α).run (generatorData n) bits ticks = _ at accepted
  rw [emptyGenerator_run] at accepted
  split_ifs at accepted <;> cases accepted

theorem empty_word_mem_pgUpTo {α : Type} [Fintype α] : ({[]} : Language α) ∈ PGUpTo α := by
  refine ⟨emptyWordUpToFamily α, ⟨1, 0, by decide⟩, ?_⟩
  intro n
  apply Machine.TimeBound.acceptingTimeBound
  intro bits
  exact ⟨.accepted [], rfl⟩

/-- Every NP language over a nonempty finite alphabet has an actual cumulative-slice generator.  The
shortest fallback word, including the empty word when present, is part of the
one finite control table shared by every index. -/
theorem np_subset_pgUpTo_nonempty {α : Type} [Fintype α] [Nonempty α] : NP α ⊆ PGUpTo α := by
  classical
  intro L np
  by_cases nonempty : L.Nonempty
  · obtain ⟨M, p, time, language⟩ := np
    have lengths : ∃ n, ∃ word ∈ L, word.length = n := by
      obtain ⟨word, member⟩ := nonempty
      exact ⟨word.length, word, member, rfl⟩
    obtain ⟨fallback, member, length⟩ := Nat.find_spec lengths
    have shortest : ∀ word ∈ L, fallback.length ≤ word.length := by
      intro word wordMember
      rw [length]
      exact Nat.find_min' lengths ⟨word, wordMember, rfl⟩
    exact UpToPolynomialGeneration.mem_pgUpTo α L M p time language fallback member shortest
  · have empty : L = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    simpa [empty] using (empty_mem_pgUpTo (α := α))

/-- Polynomial-time cumulative generation and NP coincide over every finite
alphabet, including an empty alphabet. -/
theorem np_subset_pgUpTo {α : Type} [Fintype α] : NP α ⊆ PGUpTo α := by
  classical
  cases isEmpty_or_nonempty α with
  | inr inhabited =>
      letI := inhabited
      exact np_subset_pgUpTo_nonempty
  | inl empty =>
      letI := empty
      intro L _
      have only (word : Word α) : word = [] := by
        cases word with
        | nil => rfl
        | cons letter tail => exact isEmptyElim letter
      by_cases member : [] ∈ L
      · have language : L = {[]} := by
          ext word
          rw [only word]
          simp [member]
        simpa [language] using (empty_word_mem_pgUpTo (α := α))
      · have language : L = ∅ := by
          ext word
          rw [only word]
          simp [member]
        simpa [language] using (empty_mem_pgUpTo (α := α))

/-- Polynomial-time specialisation of the time part of Proposition 4.2.  The
proof uses native machines and does not assert linear simulation overhead. -/
theorem pgUpTo_eq_np {α : Type} [Fintype α] : PGUpTo α = NP α :=
  Set.Subset.antisymm pgUpTo_subset_np np_subset_pgUpTo

theorem np_subset_pgUpTo_bool : NP Bool ⊆ PGUpTo Bool := np_subset_pgUpTo

theorem pgUpTo_eq_np_bool : PGUpTo Bool = NP Bool := pgUpTo_eq_np


end
end ComplexityOfGenerators
