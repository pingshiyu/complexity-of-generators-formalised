import ComplexityOfGenerators.Foundations.ResourceBounds
import Mathlib.Logic.Relation

/-!
# Self-reductions and the retained exact-recursive interface

`SelfReduction` and `PolynomialSelfReduction` formalise the semantic and
native computational conditions of the current Definition 6.2. Certificate
sets include the empty word, so zero certificate length does not imply that
an instance is outside the language. The ancestor, base and inverse-fibre
sets below are those used by the current Definition 6.3.

`ExactRecursiveGenerators` retains the stronger historical interface with
all-label inverse calls and finite-trial budgets. `PaperSelfReducibility`
provides the current bounded-label, accepting-time interface. The native
normalisation in `Proofs.PaperExactRecursiveGeneration` proves their
language-level equivalence and the current Proposition 6.2.
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

/-- The certificate equation and size conditions of current Definition 6.2.
`split` is the elementwise certificate decomposition, including at rank zero. -/
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

/-- Native computational clauses of current Definition 6.2. Unary outputs
represent the polynomially bounded rank and width functions. The verifier
decides the entire certificate set, including the zero-certificate test. -/
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

/-- The partial iterated reduction in current Definition 6.2. A recursive
call requires a nonempty suffix, preventing a zero-width loop. -/
inductive Iterated : Word α → Word α → Word α → Prop
  | single (x w) (length : w.length = R.width x) : Iterated x w (R.reduce x w)
  | more (x w rest y) (length : w.length = R.width x) (remaining : rest ≠ [])
      (tail : Iterated (R.reduce x w) rest y) : Iterated x (w ++ rest) y

/-- The ancestor set in current Definition 6.3, with a nonempty iterated
reduction input. Its path presentation is proved in `Proofs.SelfReduction`. -/
def ancestors (n : ℕ) : Language α :=
  {y | y ∈ L ∧ (y.length = n ∨
    ∃ x ∈ lengthSlice L n, ∃ w, w ≠ [] ∧ R.Iterated x w y)}

/-- The base sampling language in current Definition 6.3. -/
def bases (n : ℕ) : Language α := {y | y ∈ R.ancestors n ∧ R.rank y = 0}

/-- The inverse fibre in current Definition 6.3. Empty labels are included
in the semantic set; terminating walks use positive-width reductions. -/
def inverseFibre (n : ℕ) (y w : Word α) : Language α :=
  {x | x ∈ R.ancestors n ∧ R.reduce x w = y ∧ w.length = R.width x}

end SelfReduction

/-- The retained historical exact-recursive interface has one native
inverse machine for all labels and polynomial finite-trial budgets in `n`.
Ordinary and auxiliary tapes carry the two word parameters, and the unary
index tape carries `n`. `PaperExactRecursiveGenerators` supplies the current
bounded-label, accepting-time interface; `Proofs.PaperExactRecursiveGeneration`
proves the native normalisation between them. -/
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

/-- Exact recursive generability under the retained all-label,
finite-trial interface. The current criterion is
`PaperExactlyRecursivelyGenerable` in `PaperSelfReducibility`; their equivalence
and the current Proposition 6.2 are proved in
`Proofs.PaperExactRecursiveGeneration`. -/
def ExactlyRecursivelyGenerable {α : Type} [Fintype α] (L : Language α) : Prop :=
  ∃ R : SelfReduction L, Nonempty (PolynomialSelfReduction R) ∧
    Nonempty (ExactRecursiveGenerators R)

end ComplexityOfGenerators
