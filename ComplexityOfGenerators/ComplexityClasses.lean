import ComplexityOfGenerators.Generators

/-!
# Resource bounds and language classes

`PolynomialBound` uses `c * (n + 1)^k`. These bounds are cofinal among polynomial
upper bounds, absorb multiplicative constants, and make sense at size zero.

For generators, `RunsInTime` follows **Remark 1** with separate random-tape and
execution budgets. A full trial accepts exactly when the slice is nonempty,
and otherwise rejects by exhaustion. Both budgets are uniform polynomials in
`PolynomialTime`. Keeping them separate permits setup and simulation overhead
without supplying extra random bits that must also be consumed. Decision
machines use the ordinary worst-case `Machine.TimeBound` instead.
-/

namespace ComplexityOfGenerators

structure PolynomialBound where
  coefficient : ℕ
  degree : ℕ
  coefficient_pos : 0 < coefficient

def PolynomialBound.eval (p : PolynomialBound) (n : ℕ) : ℕ :=
  p.coefficient * (n + 1) ^ p.degree

instance : CoeFun PolynomialBound (fun _ => ℕ → ℕ) := ⟨PolynomialBound.eval⟩

/-- Remark 1 trials with distinct seed and primitive-transition budgets. -/
def Machine.GeneratorTimeBound {I A O : Type} (M : Machine I A O)
    (data : InputData I A) (seedBudget timeBudget : ℕ) : Prop :=
  (∀ b, b.length ≤ seedBudget → M.HaltsWithin data b timeBudget) ∧
  (∀ b, b.length = seedBudget → (M.Accepts data b ↔ (M.generatedLanguage data).Nonempty))

/-- Short name used in the trial-budget lemmas. -/
abbrev Machine.TrialBound {I A O : Type} (M : Machine I A O) := M.GeneratorTimeBound

/-- The emptiness test asserted in Remark 1, proved from the budget convention
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

/-- Definition 4.3 with the empty-slice convention of Remark 1.
This also explicitly rules out accepting only a proper subset of full-budget seeds. -/
def RunsInTime (G : UniformGenerators α) (seed time : ℕ → ℕ) : Prop :=
  ∀ n, G.machine.GeneratorTimeBound (generatorData n) (seed n) (time n)

/-- Definition 5.1 with the approved Remark 1 interpretation: uniform polynomial
seed and execution budgets for the whole family. -/
def PolynomialTime (G : UniformGenerators α) : Prop :=
  ∃ seed time : PolynomialBound, G.RunsInTime seed time

/-- Definition 4.4: work space only; output and random tapes are not counted. -/
def RunsInSpace (G : UniformGenerators α) (s : ℕ → ℕ) : Prop :=
  ∀ n, G.machine.SpaceBound (generatorData n) (s n)

def PolynomialSpace (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound, G.RunsInSpace p

end UniformGenerators

variable (α : Type) [Fintype α]

/-- Definition 3.3: a deterministic Turing recogniser may diverge off the language. -/
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

/-- Definition 4.3 with the approved separate trial budgets: exact-length,
uniform, time-bounded generation. This extends the paper's domain of
time-constructible bounds to arbitrary `t`; constructibility is not encoded. -/
def GTIME (t : ℕ → ℕ) : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧
      ∃ seed : ℕ → ℕ, (∀ n, 0 < seed n) ∧ G.toUniformGenerators.RunsInTime seed t }

/-- Definition 4.4: exact-length, uniform, space-bounded generation. This extends
the paper's domain of space-constructible bounds to arbitrary `s`;
constructibility is not encoded. -/
def GSPACE (s : ℕ → ℕ) : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.RunsInSpace s }

/-- Definition 5.2: polynomial-time generable languages. -/
def PG : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.PolynomialTime }

/-- Definition 6.2: polynomial-space generable languages. -/
def PSPACEG : LanguageClass α :=
  { L | ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.PolynomialSpace }

end ComplexityOfGenerators
