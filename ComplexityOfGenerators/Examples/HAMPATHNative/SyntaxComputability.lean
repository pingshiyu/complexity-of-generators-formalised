import ComplexityOfGenerators.Examples.HAMPATHNative.SyntaxBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

theorem wellFormed_eq_decode (word : List Symbol) : wellFormed word = (decode word).isSome := by
  have good := wellFormed_iff_decode word
  cases left : wellFormed word <;> cases right : (decode word).isSome <;> simp_all

theorem syntaxWord_decode (word : List Symbol) :
    syntaxWord word = if (decode word).isSome then [()] else [] := by
  rw [syntaxWord, wellFormed_eq_decode]

/-- A concrete native polynomial procedure for canonical graph syntax. -/
noncomputable def syntax_decode_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => if (decode word).isSome then [()] else []) := by
  simpa only [syntaxWord_decode] using syntax_computable

end ComplexityOfGenerators.Examples.HAMPATH.Native
