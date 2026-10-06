import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import Mathlib.Computability.TuringMachine.Computable

/-!
# Existing computability and encoding APIs

Mathlib already provides finite encodings, partial recursive functions, recursive
enumerability, Rice's theorem, and many-one reductions. Reuse those definitions
when proving Theorem 3.1, rather than developing a second computability theory.
The bridge from this project's machine evaluator to Mathlib's partial-recursive
semantics is still a separate construction obligation.
-/

namespace ComplexityOfGenerators.ComputabilityFoundation

abbrev Encoding := Computability.Encoding
abbrev PolynomialTimeComputable {α β Γ Δ : Type}
    (input : α → List Γ) (output : β → List Δ) (f : α → β) :=
  Turing.TM2ComputableInPolyTime input output f

abbrev RecursivelyEnumerable {α : Type*} [Primcodable α] (p : α → Prop) := REPred p
abbrev DecidableComputably {α : Type*} [Primcodable α] (p : α → Prop) := ComputablePred p

/-- Post's theorem: a predicate is decidable exactly when it and its complement
are recursively enumerable, in Mathlib's partial-recursive model. -/
theorem post {α : Type*} [Primcodable α] (p : α → Prop) :
    DecidableComputably p ↔ RecursivelyEnumerable p ∧
      RecursivelyEnumerable (fun x => ¬ p x) :=
  ComputablePred.computable_iff_re_compl_re'

/-- The universal machine's halting predicate is recursively enumerable. -/
theorem halting_recursively_enumerable (n : ℕ) :
    RecursivelyEnumerable (fun c => (Nat.Partrec.Code.eval c n).Dom) :=
  ComputablePred.halting_problem_re n

/-- The same predicate is undecidable. -/
theorem halting_undecidable (n : ℕ) :
    ¬ DecidableComputably (fun c => (Nat.Partrec.Code.eval c n).Dom) :=
  ComputablePred.halting_problem n

/-- Mathlib's recursion-theoretic many-one reductions, distinct from Karp
reductions: no polynomial resource bound is present in this definition. -/
abbrev ComputableManyOneReduction {α β : Type*} [Primcodable α] [Primcodable β]
    (p : α → Prop) (q : β → Prop) := ManyOneReducible p q

end ComplexityOfGenerators.ComputabilityFoundation
