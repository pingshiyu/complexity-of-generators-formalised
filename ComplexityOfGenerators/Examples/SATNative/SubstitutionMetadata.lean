import ComplexityOfGenerators.Examples.SATNative.SubstitutionLiteralCorrect

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeAssignment

set_option backward.isDefEq.respectTransparency false

theorem metadata_eq (s : Store) (active : ℕ) (literal : Literal)
    (count : s 10 = List.replicate active .one)
    (index : s 5 = List.replicate (literalIndex literal) .one) (tag : s 11 = [literalTag literal]) :
    metadata s active literal = s := by
  funext j
  by_cases a : j = 10 <;> by_cases b : j = 5 <;> by_cases c : j = 11 <;>
    simp [metadata, a, b, c] <;> first | exact count.symm | exact index.symm | exact tag.symm

theorem substituteLiteral_buffer_of_fields {O : Type} (bit : Bool) (s : Store) (capacity active : ℕ) (literal : Literal)
    (cap : s 4 = List.replicate capacity .one) (count : s 10 = List.replicate active .one)
    (index : s 5 = List.replicate (literalIndex literal) .one) (tag : s 11 = [literalTag literal]) :
    (substituteLiteral (O := O) bit).eval s 21 = ((literal.substitute active bit).encode capacity).reverse ++ s 21 := by
  have transformed := substituteLiteral_buffer (O := O) bit s capacity active literal cap
  rw [metadata_eq s active literal count index tag] at transformed
  exact transformed

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
