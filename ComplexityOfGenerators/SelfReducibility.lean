import ComplexityOfGenerators.Foundations.ResourceBounds
import Mathlib.Logic.Relation

/-!
# Self-reductions (Appendix A.23)

The certificate sets in this appendix contain the empty certificate, unlike
`PolynomialVerifier` in Section 7. In particular, a zero certificate length
does not mean that an instance is outside the language.

`SelfReduction` records the semantic conditions of Definition A.23.1.
Computational witnesses are separate: `PolynomialSelfReduction` requires
actual deterministic native machines for the verifier and all three functions.
Neither structure assumes a generator for the language.
-/

namespace ComplexityOfGenerators

/-- A deterministic polynomial-time function of two word arguments, represented
by a native transducer. Both input lengths are charged. -/
structure PolynomialWordFunction {I A O : Type} (f : Word I → Word A → Word O) where
  machine : Machine I A O
  deterministic : machine.Deterministic
  time : PolynomialBound
  timeBound : ∀ x y, machine.TimeBound { input := x, auxiliary := y }
    (time (x.length + y.length))
  computes : ∀ x y, machine.Produces { input := x, auxiliary := y } [] (f x y)

/-- The certificate equation and size conditions in Definition A.23.1.
`split` is the elementwise form of Equation (1), including at rank zero. -/
structure SelfReduction {α : Type} (L : Language α) where
  certificates : Word α → Set (Word α)
  rank : Word α → ℕ
  width : Word α → ℕ
  reduce : Word α → Word α → Word α
  certifies : ∀ x, x ∈ L ↔ (certificates x).Nonempty
  certificate_length : ∀ x c, c ∈ certificates x → c.length = rank x
  split : ∀ x c, c ∈ certificates x ↔
    ∃ w d, w.length = width x ∧ d ∈ certificates (reduce x w) ∧ c = w ++ d
  positive : ∀ x, 0 < rank x ↔ 0 < width x
  length_reduce : ∀ x w, (reduce x w).length ≤ x.length
  rank_reduce : ∀ x w, rank (reduce x w) ≤ rank x - width x
  rankBound : PolynomialBound
  rank_le : ∀ x, rank x ≤ rankBound x.length
  logCoefficient : ℕ
  logConstant : ℕ
  width_le : ∀ x, width x ≤ logCoefficient * Nat.log 2 (x.length + 1) + logConstant

/-- Computational clauses of Definition A.23.1. Unary outputs represent the
natural-valued functions; their values are already polynomially bounded.
The verifier decides membership in the entire certificate set, including `[]`.
Its time bound also supplies item (2), the zero-certificate test. -/
structure PolynomialSelfReduction {α : Type} {L : Language α} (R : SelfReduction L) where
  verifier : Machine α α Unit
  verifier_deterministic : verifier.Deterministic
  verifierTime : PolynomialBound
  verifier_time : ∀ x c, verifier.TimeBound { input := x, auxiliary := c }
    (verifierTime (x.length + c.length))
  verifier_correct : ∀ x c,
    verifier.Accepts { input := x, auxiliary := c } [] ↔ c ∈ R.certificates x
  rank_computable : PolynomialWordFunction
    (fun (x : Word α) (_ : Word Unit) => List.replicate (R.rank x) ())
  width_computable : PolynomialWordFunction
    (fun (x : Word α) (_ : Word Unit) => List.replicate (R.width x) ())
  reduction_computable : PolynomialWordFunction R.reduce

namespace SelfReduction

variable {α : Type} {L : Language α} (R : SelfReduction L)

/-- A reduction consuming a nonempty certificate prefix. Zero-width calls
are deliberately excluded: they need not decrease certificate length. -/
def Step (x y : Word α) : Prop :=
  ∃ w, 0 < R.width x ∧ w.length = R.width x ∧ R.reduce x w = y

/-- A finite sequence of positive-prefix reductions. -/
abbrev Path := Relation.ReflTransGen R.Step

/-- Definition A.23.2 as a graph of the partial iterated reduction. The second
branch is used only when a nonempty suffix remains. This avoids defining a
nonterminating Lean function at zero-width inputs. -/
inductive Iterated : Word α → Word α → Word α → Prop
  | single (x w) (length : w.length = R.width x) : Iterated x w (R.reduce x w)
  | more (x w rest y) (length : w.length = R.width x) (remaining : rest ≠ [])
      (tail : Iterated (R.reduce x w) rest y) : Iterated x (w ++ rest) y

/-- Definition A.23.4, with the paper's nonempty iterated-reduction input.
The path presentation is proved equivalent in `Proofs.SelfReduction`. -/
def ancestors (n : ℕ) : Language α :=
  {y | y ∈ L ∧ (y.length = n ∨
    ∃ x ∈ lengthSlice L n, ∃ w, w ≠ [] ∧ R.Iterated x w y)}

/-- The initial sampling language in Definition A.23.5. -/
def bases (n : ℕ) : Language α := {y | y ∈ R.ancestors n ∧ R.rank y = 0}

/-- The exact inverse fibre in Definition A.23.5. Empty labels are retained
here, even though a terminating construction must avoid their zero-rank loops. -/
def inverseFibre (n : ℕ) (y w : Word α) : Language α :=
  {x | x ∈ R.ancestors n ∧ R.reduce x w = y ∧ w.length = R.width x}

end SelfReduction

/-- Definition A.23.5, with a single native machine for all inverse parameters.
The two word parameters occupy its ordinary and auxiliary input tapes; `n`
uses the existing unary index tape. Bounds are uniform polynomials in `n`.
As elsewhere in this repo, the empty-fibre case uses Remark 1 trial bounds. -/
structure ExactRecursiveGenerators {α : Type} [Fintype α] {L : Language α}
    (R : SelfReduction L) where
  base : UniformGenerators α
  baseTime : base.PolynomialTime
  base_language : ∀ n, base.layer n = R.bases n
  inverse : Machine α α α
  inverseSeed : PolynomialBound
  inverseTime : PolynomialBound
  inverse_generator : ∀ n y w, y ∈ L →
    inverse.IsGenerator { input := y, auxiliary := w, index := n }
  inverse_language : ∀ n y w, y ∈ L →
    inverse.generatedLanguage { input := y, auxiliary := w, index := n } =
      R.inverseFibre n y w
  inverse_time : ∀ n y w, y ∈ L →
    inverse.GeneratorTimeBound { input := y, auxiliary := w, index := n }
      (inverseSeed n) (inverseTime n)

/-- Exact recursive generability, without adding a `PG` witness or an assumed
compiler to the paper's hypotheses. -/
def ExactlyRecursivelyGenerable {α : Type} [Fintype α] (L : Language α) : Prop :=
  ∃ R : SelfReduction L, Nonempty (PolynomialSelfReduction R) ∧
    Nonempty (ExactRecursiveGenerators R)

end ComplexityOfGenerators
