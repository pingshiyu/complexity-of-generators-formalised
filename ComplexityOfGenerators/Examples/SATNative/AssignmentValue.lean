import ComplexityOfGenerators.Examples.SATNative.AssignmentLookup

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def literalTag : Literal → Symbol
  | .constant true => .trueConstant
  | .constant false => .falseConstant
  | .var _ true => .positive
  | .var _ false => .negative

def literalIndex : Literal → ℕ
  | .constant _ => 0
  | .var j _ => j

theorem literalValue_correct {O : Type} (s : Store) (bits : List Bool) (lit : Literal)
    (valid : lit.valid bits.length) (certificate : s 3 = bits.map bitSymbol)
    (active : (s 10).length = bits.length) (index : (s 5).length = literalIndex lit)
    (tag : (s 11).head? = some (literalTag lit)) :
    (literalValue (O := O)).eval s 26 = if lit.eval (assignment bits) then [.one] else [] := by
  rw [literalValue_result]
  cases lit with
  | constant bit => cases bit <;> simp [value, tag, literalTag, Literal.eval]
  | var position sign =>
    have selected := lookup_certificate (O := O) s bits position certificate active index valid.1 valid.2
    have bit : ((s 3).drop ((s 10).length - (s 5).length)).head? =
        some (bitSymbol (assignment bits position)) := by
      simpa only [lookup_eval, Function.update_self] using selected
    rw [bit]
    cases sign <;> cases assignmentValue : assignment bits position <;>
      simp [value, tag, literalTag, bitSymbol, Literal.eval, assignmentValue]

/-- Evaluating a literal touches only local scratch/output registers, so the
syntax parser's flags, its source suffix and its loop clock are preserved. -/
theorem literalValue_frame {O : Type} (s : Store) (j : Fin 32)
    (scratch : j ≠ 9) (clock : j ≠ 22) (temporary : j ≠ 23) (discarded : j ≠ 24)
    (lookupResult : j ≠ 25) (result : j ≠ 26) :
    (literalValue (O := O)).eval s j = s j := by
  cases tag : (s 11).head? with
  | none => simp [literalValue, Routine.seq, lookup_eval, Routine.clear, Routine.ofLocal,
      valueCode, Local.eval, tag, scratch, clock, temporary, discarded, lookupResult, result]
  | some symbol =>
    cases symbol <;> by_cases bit : (s 3)[(s 10).length - (s 5).length]? = some .one <;>
      simp [literalValue, Routine.seq, lookup_eval, Routine.clear, Routine.ofLocal,
        valueCode, Local.eval, Local.push, Action.apply, tag, bit,
        scratch, clock, temporary, discarded, lookupResult, result]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment
