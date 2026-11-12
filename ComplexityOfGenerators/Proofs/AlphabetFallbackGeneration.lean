import ComplexityOfGenerators.Simulation.AlphabetFallback.Language
import ComplexityOfGenerators.Simulation.FiniteExactWordSampler
import ComplexityOfGenerators.Proofs.GeneratorCriteria
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! Polynomial generation of an NP language augmented by a constant-word
fallback. The empty-word boundary is determined by one finite control bit. -/

namespace ComplexityOfGenerators

variable {α : Type} [Fintype α]

/-- Positive constant words over an arbitrary finite alphabet. -/
def constantLetterLanguage (letter : α) : Language α :=
  {word | word≠[] ∧ ∀ a∈word,a=letter}

namespace AlphabetFallbackGeneration

open Simulation
open Simulation.AlphabetFallback
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable [Nonempty α] (L : Language α) (M : Machine α Bool Unit) (p : PolynomialBound)
    (time : ∀ word, M.TimeBound (decisionData word) (p word.length))
    (language : ∀ word, (∃ bits, M.Accepts (decisionData word) bits) ↔ word ∈ L)
    (bit : α)

local instance : Decidable ([] ∈ L) := Classical.propDecidable _

def npFallback := fallbackGenerator (FiniteExactWordSampler.sampler α) M bit (decide ([] ∈ L))

def fallbackSeed (α : Type) [Fintype α] (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (Polynomial.C (4*(Fintype.card α+2)+2)*Polynomial.X+p.asPolynomial+4)

/-- Bank-instruction budget, including draining all supplied random bits. -/
def fallbackTicksPolynomial (α : Type) [Fintype α] (p : PolynomialBound) : Polynomial ℕ :=
  Polynomial.C (5*(Fintype.card α+2)+10)*Polynomial.X+5*p.asPolynomial + (fallbackSeed α p).asPolynomial + 30

/-- Native scan overhead applied to the bank-instruction budget. -/
def fallbackTimePolynomial (α : Type) [Fintype α] (p : PolynomialBound) : Polynomial ℕ :=
  let ticks := fallbackTicksPolynomial α p
  1 + (ticks + 1) * (2 * ticks + 4)

def fallbackTime (α : Type) [Fintype α] (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (fallbackTimePolynomial α p)

omit [Nonempty α] in
theorem fallbackSeed_bound (n : ℕ) : (4*(Fintype.card α+2)+2)*n+p n+4 ≤ fallbackSeed α p n := by
  have bound := PolynomialBound.eval_le_ofPolynomial (Polynomial.C (4*(Fintype.card α+2)+2)*Polynomial.X+p.asPolynomial+4) n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,Polynomial.eval_C,
    PolynomialBound.asPolynomial_eval] at bound
  exact bound

omit [Nonempty α] in
theorem fallbackTime_bound (n : ℕ) :
    let t := (5*(Fintype.card α+2)+10)*n+5*p n + fallbackSeed α p n + 30
    1 + (t + 1) * (2 * t + 4) ≤ fallbackTime α p n := by
  have bound := PolynomialBound.eval_le_ofPolynomial (fallbackTimePolynomial α p) n
  simp only [fallbackTimePolynomial, fallbackTicksPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,Polynomial.eval_C, Polynomial.eval_one,
    PolynomialBound.asPolynomial_eval] at bound
  exact bound

include time language

theorem npFallback_execution (n : ℕ) (bits : BitString) :
    ∃ ticks result, ticks ≤ 1 + (((5*(Fintype.card α+2)+10)*n+5*p n + bits.length + 30) + 1) *
        (2 * ((5*(Fintype.card α+2)+10)*n+5*p n + bits.length + 30) + 4) ∧
      (npFallback L M bit).run (generatorData n) bits ticks = .halted result ∧
      (match result with
        | .accepted word => word ∈ lengthSlice (L ∪ constantLetterLanguage bit) n
        | .rejected => False
        | .exhausted => (n = 0 ∧ [] ∉ L) ∨ bits.length ≤ (4*(Fintype.card α+2)+2)*n+p n+3) := by
  by_cases live : n ≠ 0 ∨ [] ∈ L
  · obtain ⟨ticks, result, cost, execution, related⟩ := fallback_executes_live (FiniteExactWordSampler.sampler α) M bit (decide ([] ∈ L)) n ((Fintype.card α+2)*n) (p n) bits
      (live.imp id (by simp)) (FiniteExactWordSampler.sampler_run α n)
      (fun word length => by simpa [length] using time word)
    obtain ⟨nativeTicks, nativeCost, native⟩ := TransducerBank.bank_run (fallbackBank (FiniteExactWordSampler.sampler α) M bit (decide ([] ∈ L))) _ bits ticks result execution
    refine ⟨nativeTicks, result, nativeCost.trans (by nlinarith), native, ?_⟩
    cases result with
    | rejected => exact related
    | exhausted => exact Or.inr (by nlinarith [related])
    | accepted word =>
        obtain ⟨length, member⟩ := related
        refine ⟨?_, length⟩
        rcases member with accepted | constant
        · exact Or.inl ((language word).mp accepted)
        · by_cases zero : n = 0
          · have empty : [] ∈ L := live.resolve_left (by simp [zero])
            exact Or.inl (by simpa [constant, zero] using empty)
          · right
            subst word
            exact ⟨by simpa using zero, fun letter member => (List.mem_replicate.mp member).2⟩
  · have zero : n = 0 := by tauto
    have absent : [] ∉ L := by tauto
    subst n
    obtain ⟨ticks, cost, execution⟩ := fallback_executes_empty (FiniteExactWordSampler.sampler α) M bit bits
    obtain ⟨nativeTicks, nativeCost, native⟩ := TransducerBank.bank_run (fallbackBank (FiniteExactWordSampler.sampler α) M bit false) _ bits ticks .exhausted execution
    refine ⟨nativeTicks, .exhausted, nativeCost.trans ?_, ?_, Or.inl ⟨rfl, absent⟩⟩
    · have upper : ticks ≤ (5*(Fintype.card α+2)+10)*0+5*p 0 + bits.length + 30 := by omega
      gcongr
    · unfold npFallback fallbackGenerator
      generalize flag : decide ([] ∈ L) = allow
      have equal : allow = false := flag.symm.trans (decide_eq_false absent)
      clear flag
      subst allow
      exact native

theorem npFallback_language (n : ℕ) :
    (npFallback L M bit).generatedLanguage (generatorData n) = lengthSlice (L ∪ constantLetterLanguage bit) n := by
  ext word
  constructor
  · rintro ⟨bits, _, t, accepted⟩
    obtain ⟨ticks, result, _, native, related⟩ := npFallback_execution L M p time language bit n bits
    have same := (npFallback L M bit).halted_outcome_unique _ bits t ticks _ _ accepted native
    subst result
    exact related
  · rintro ⟨member, length⟩
    rcases member with member | ⟨nonempty, constant⟩
    · apply fallback_contains_np_word (FiniteExactWordSampler.sampler α) M bit (decide ([] ∈ L)) n word
        (by rw [FiniteExactWordSampler.sampler_language];exact length)
      · by_cases zero : n = 0
        · right
          have empty : word = [] := List.length_eq_zero_iff.mp (length.trans zero)
          simp only [decide_eq_true_eq]
          simpa [empty] using member
        · exact Or.inl zero
      · exact (language word).mpr member
    · have equal : word = List.replicate n bit := List.eq_replicate_iff.mpr ⟨length, constant⟩
      rw [equal]
      apply fallback_contains_constant (FiniteExactWordSampler.sampler α) M bit (decide ([] ∈ L)) n (p n)
      · intro zero
        exact nonempty (by simp [equal, zero])
      · rw [FiniteExactWordSampler.sampler_language];simp
      · simpa using time (List.replicate n bit)

theorem npFallback_never_rejects (n : ℕ) (bits : BitString) (t : ℕ) :
    (npFallback L M bit).run (generatorData n) bits t ≠ .halted .rejected := by
  intro rejected
  obtain ⟨ticks, result, _, native, related⟩ := npFallback_execution L M p time language bit n bits
  have same := (npFallback L M bit).halted_outcome_unique _ bits t ticks _ _ rejected native
  subst result
  exact related

theorem npFallback_full_trial (n : ℕ) (bits : BitString) (long : (4*(Fintype.card α+2)+2)*n+p n+3 < bits.length) :
    (npFallback L M bit).Accepts (generatorData n) bits ↔
      ((npFallback L M bit).generatedLanguage (generatorData n)).Nonempty := by
  constructor
  · intro accepted
    exact (Machine.generatedLanguage_nonempty_iff_accepts _ _).mpr ⟨bits, accepted⟩
  · intro nonempty
    obtain ⟨ticks, result, _, native, related⟩ := npFallback_execution L M p time language bit n bits
    cases result with
    | accepted word => exact ⟨word, ticks, native⟩
    | rejected => exact False.elim related
    | exhausted =>
        rcases related with ⟨zero, absent⟩ | short
        · rw [npFallback_language L M p time language bit n] at nonempty
          obtain ⟨word, member, length⟩ := nonempty
          have empty : word = [] := List.length_eq_zero_iff.mp (length.trans zero)
          subst word
          rcases member with member | member
          · exact False.elim (absent member)
          · exact False.elim (member.1 rfl)
        · omega

theorem npFallback_isGenerator (n : ℕ) : (npFallback L M bit).IsGenerator (generatorData n) := by
  apply Machine.isGenerator_of_full_trials _ _ ((4*(Fintype.card α+2)+2)*n+p n+4)
  · refine ⟨?_, npFallback_never_rejects L M p time language bit n⟩
    intro bits
    obtain ⟨ticks, result, _, native, _⟩ := npFallback_execution L M p time language bit n bits
    exact ⟨ticks, result, native⟩
  · intro bits length
    exact npFallback_full_trial L M p time language bit n bits (by omega)

theorem npFallback_trialBound (n : ℕ) : (npFallback L M bit).GeneratorTimeBound (generatorData n) (fallbackSeed α p n) (fallbackTime α p n) := by
  constructor
  · intro bits length
    obtain ⟨ticks, result, cost, native, _⟩ := npFallback_execution L M p time language bit n bits
    have upper : ticks ≤ fallbackTime α p n := by
      apply le_trans cost
      apply le_trans _ (fallbackTime_bound (α:=α) p n)
      gcongr
    exact (npFallback L M bit).haltsWithin_mono _ bits upper ⟨result, native⟩
  · intro bits length
    apply npFallback_full_trial L M p time language bit n bits
    have lower := fallbackSeed_bound (α:=α) p n
    omega

omit L M p time language in
/-- Every native NP language becomes polynomially generable after adding one
constant-word fallback at each positive length. -/
theorem np_union_constantLetter_mem_pg {L : Language α} (member : L ∈ NP α) (bit : α) :
    L ∪ constantLetterLanguage bit ∈ PG α := by
  obtain ⟨M, p, time, language⟩ := member
  exact mem_pg_of_lengthSlices (L ∪ constantLetterLanguage bit) (npFallback L M bit)
    (fallbackSeed α p) (fallbackTime α p)
    (npFallback_isGenerator L M p time language bit)
    (npFallback_language L M p time language bit)
    (npFallback_trialBound L M p time language bit)

end
end AlphabetFallbackGeneration
end ComplexityOfGenerators
