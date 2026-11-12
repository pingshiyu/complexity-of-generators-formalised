import ComplexityOfGenerators.Examples.HAMPATHNative.Metadata
import ComplexityOfGenerators.Examples.HAMPATHNative.Logarithm
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel
import ComplexityOfGenerators.Examples.HAMPATHNative.Syntax
import ComplexityOfGenerators.Examples.HAMPATHWordReduction

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem wordWidth_eq_header (word : List Symbol) :
    wordWidth word = if wellFormed word then Nat.clog 2 (headerSize word) else 0 := by
  cases decoded : decode word with
  | none =>
      have invalid : wellFormed word = false := by
        cases valid : wellFormed word with
        | false => rfl
        | true => have good := (wellFormed_iff_decode word).mp valid; simp [decoded] at good
      simp [wordWidth, decoded, invalid]
  | some pair =>
      obtain ⟨graph, start⟩ := pair
      obtain ⟨inside, encoded⟩ := decode_sound decoded
      rw [← encoded]
      simp [wordWidth_encode graph start inside, headerSize_encode, wellFormed_encode graph start inside, width]

noncomputable def widthCore {O : Type} : Routine Symbol O 32 :=
  metadata.seq (Logarithm.routine.seq (gate 19))

theorem widthCore_value {O : Type} (s : Store) :
    (widthCore (O := O)).eval s 19 =
      if acceptedSyntax s then List.replicate (Nat.clog 2 (s 4).length) (.bit true) else [] := by
  let a := (metadata (O := O)).eval s
  let b := (Logarithm.routine (O := O)).eval a
  have flagValue : b 16 = flag (acceptedSyntax s) :=
    (Logarithm.routine_frame (O := O) a 16 (by decide) (by decide) (by decide)).trans
      (by simp [a, metadata_eval])
  have output : b 19 = List.replicate (Nat.clog 2 (s 4).length) (.bit true) := by
    have value := Logarithm.routine_value (O := O) a
    simpa [b, a, metadata_eval] using value
  change (gate (O := O) 19).eval b 19 = _
  rw [gate_eval, flagValue, output]
  cases acceptedSyntax s <;> simp [flag]

noncomputable def widthRoutine : Routine Symbol Unit 32 :=
  prepare.seq (parser.seq widthCore)

theorem widthRoutine_value (word : List Symbol) (auxiliary : List Unit) :
    widthRoutine.eval (loaded word auxiliary).store 19 = List.replicate (wordWidth word) (.bit true) := by
  let s := (prepared word auxiliary).store
  have wordEq : s 2 = word := prepared_word word auxiliary
  have syntaxValue : acceptedSyntax ((parser (O := Unit)).eval s) = wellFormed word := by
    simpa only [acceptedSyntax, wordEq] using parser_decides (O := Unit) s
  have size : (((parser (O := Unit)).eval s) 4).length = headerSize word := by
    rw [parser_eval]
    simp [s, startEncoded, rowEncoded, cellEncoded, prepared_word]
  change (widthCore (O := Unit)).eval ((parser (O := Unit)).eval s) 19 = _
  rw [widthCore_value, syntaxValue, size, wordWidth_eq_header]
  cases wellFormed word <;> simp

end ComplexityOfGenerators.Examples.HAMPATH.Native
