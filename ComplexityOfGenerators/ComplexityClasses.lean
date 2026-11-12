import ComplexityOfGenerators.Generators

/-!
# Resource bounds and language classes

`PolynomialBound` uses `c * (n + 1)^k`. These bounds are cofinal among polynomial
upper bounds, absorb multiplicative constants, and make sense at size zero.

The internal `RunsInTime` interface retains separate random-tape and execution
budgets. A full trial accepts exactly when the slice is nonempty, and otherwise
rejects by exhaustion. Both budgets are uniform polynomials in `PolynomialTime`.
This historical finite-trial interface differs from the current paper's bounds
on accepting runs; `Proofs.AcceptingTimeGeneration` proves that the resulting
PG class is the same. Keeping the budgets separate permits setup and simulation
overhead without supplying extra random bits that must also be consumed.
Decision machines use the ordinary worst-case `Machine.TimeBound` instead.
-/

namespace ComplexityOfGenerators

structure PolynomialBound where
  coefficient : ℕ
  degree : ℕ
  coefficient_pos : 0 < coefficient

def PolynomialBound.eval (p : PolynomialBound) (n : ℕ) : ℕ :=
  p.coefficient * (n + 1) ^ p.degree

instance : CoeFun PolynomialBound (fun _ => ℕ → ℕ) := ⟨PolynomialBound.eval⟩

/-- Internal finite trials with distinct seed and primitive-transition budgets. -/
def Machine.GeneratorTimeBound {I A O : Type} (M : Machine I A O)
    (data : InputData I A) (seedBudget timeBudget : ℕ) : Prop :=
  (∀ b, b.length ≤ seedBudget → M.HaltsWithin data b timeBudget) ∧
  (∀ b, b.length = seedBudget → (M.Accepts data b ↔ (M.generatedLanguage data).Nonempty))

/-- Short name used in the trial-budget lemmas. -/
abbrev Machine.TrialBound {I A O : Type} (M : Machine I A O) := M.GeneratorTimeBound

/-- The full-trial emptiness test, proved from the internal budget convention
and the operational distinction between explicit rejection and exhaustion. -/
theorem bounded_trial_exhausted_iff_empty {I A O : Type} (M : Machine I A O)
    (data : InputData I A) (seed t : ℕ) (b : BitString)
    (generator : M.IsGenerator data) (bound : M.GeneratorTimeBound data seed t)
    (length : b.length = seed) :
    M.run data b t = .halted .exhausted ↔ M.generatedLanguage data = ∅ := by
  constructor
  · intro exhausted
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have accepts := (bound.2 b length).2 ⟨w, hw⟩
    obtain ⟨w', s, hs⟩ := accepts
    have impossible := M.halted_outcome_unique data b t s .exhausted (.accepted w')
      exhausted hs
    cases impossible
  · intro empty
    obtain ⟨result, halted⟩ := bound.1 b length.le
    cases result with
    | exhausted => exact halted
    | rejected => exact False.elim ((generator.1.2 b t) halted)
    | accepted w =>
      have nonempty := (bound.2 b length).1 ⟨w, t, halted⟩
      obtain ⟨w', hw'⟩ := nonempty
      rw [empty] at hw'
      exact False.elim hw'

namespace UniformGenerators

variable {α : Type} [Fintype α]

/-- Historical finite-trial time bounds for a uniform generator family.
Full-budget seeds all accept on a nonempty slice and all exhaust on an empty one. -/
def RunsInTime (G : UniformGenerators α) (seed time : ℕ → ℕ) : Prop :=
  ∀ n, G.machine.GeneratorTimeBound (generatorData n) (seed n) (time n)

/-- Uniform polynomial seed and execution budgets for the whole family.
This internal interface characterises the accepting-time PG class of
Definitions 5.1–5.2 by `mem_pg_iff_accepting_polynomial_time`. -/
def PolynomialTime (G : UniformGenerators α) : Prop :=
  ∃ seed time : PolynomialBound, G.RunsInTime seed time

/-- The space-bound convention of Section 4: work space only; output and random
tapes are not counted. -/
def RunsInSpace (G : UniformGenerators α) (s : ℕ → ℕ) : Prop :=
  ∀ n, G.machine.SpaceBound (generatorData n) (s n)

def PolynomialSpace (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound, G.RunsInSpace p

end UniformGenerators

variable (α : Type) [Fintype α]

/-- Recursive enumerability, as used in Section 3: a deterministic Turing
recogniser may diverge off the language. -/
def RE : LanguageClass α :=
  { L | ∃ M : Machine α Bool Unit, M.Deterministic ∧
      ∀ w, M.Accepts (decisionData w) [] ↔ w ∈ L }

/-- Polynomial-time decidable languages. -/
def P : LanguageClass α :=
  { L | ∃ M : Machine α Bool Unit, ∃ p : PolynomialBound,
      M.Deterministic ∧
      (∀ w, M.TimeBound (decisionData w) (p w.length)) ∧
      (∀ w, M.Accepts (decisionData w) [] ↔ w ∈ L) }

/-- Nondeterministic polynomial time, represented by finite binary choice tapes.
All branches are time bounded; a word is accepted if some branch accepts it. -/
def NP : LanguageClass α :=
  { L | ∃ M : Machine α Bool Unit, ∃ p : PolynomialBound,
      (∀ w, M.TimeBound (decisionData w) (p w.length)) ∧
      (∀ w, (∃ b, M.Accepts (decisionData w) b) ↔ w ∈ L) }

/-- Complements are relative to **all** finite words, including malformed encodings. -/
def coNP : LanguageClass α :=
  { L | Lᶜ ∈ NP α }

/-- Deterministic polynomial-space decision, with termination on every input. -/
def PSPACE : LanguageClass α :=
  { L | ∃ M : Machine α Bool Unit, ∃ p : PolynomialBound,
      M.Deterministic ∧
      (∀ w, M.Halts (decisionData w) []) ∧
      (∀ w, M.SpaceBound (decisionData w) (p w.length)) ∧
      (∀ w, M.Accepts (decisionData w) [] ↔ w ∈ L) }

/-- The current paper's exact accepting-time convention. Only accepting runs
are bounded; rejecting/exhausting empty slices impose no deadline. The formula
is definitionally `Machine.AcceptingTimeBound`, introduced in ResourceGeneration.
Constructibility is a separate premise of resource characterisations. -/
def GTIME (t : ℕ → ℕ) : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧
      ∀ n bits word, G.machine.Produces (generatorData n) bits word →
        G.machine.run (generatorData n) bits (t n) = .halted (.accepted word) }

/-- The exact-length, uniform, space-bounded class introduced in Section 4. This extends
the paper's domain of space-constructible bounds to arbitrary `s`;
constructibility is not encoded. -/
def GSPACE (s : ℕ → ℕ) : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.RunsInSpace s }

/-- Definition 5.2: polynomial-time exact generability, using the internal
finite-trial interface. `mem_pg_iff_accepting_polynomial_time` proves equivalence
with the paper's accepting-time convention. -/
def PG : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.PolynomialTime }

/-- The retained polynomial-space exact-generation class. Its historical
PSPACE characterisation is exposed in `HistoricalTheorems`. -/
def PSPACEG : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.PolynomialSpace }

end ComplexityOfGenerators
