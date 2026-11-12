import ComplexityOfGenerators.Examples.SATNative.SubstitutionEncode

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] checkedStream

noncomputable def streamOutput (s : Store) : List Symbol :=
  let output := (checkedStream (O := Symbol)).eval s
  if NativeEvaluation.verdict output then (output 21).reverse else []

/-- Exact all-word correctness of the concrete checked substitution stream.
Malformed syntax and wrong-width/nonbinary labels produce the empty word;
rank-zero empty-label calls reproduce the original constant formula. -/
theorem streamOutput_correct (s : Store) : streamOutput s = wordReduce (s 2) (s 3) := by
  cases decoded : decode (s 2) with
  | none =>
    have flag : NativeEvaluation.verdict ((checkedStream (O := Symbol)).eval s) = false := by
      rw [checkedStream_verdict]
      simp [decoded]
    simp [streamOutput, flag, wordReduce, decoded]
  | some triple =>
    rcases triple with ⟨capacity, active, formula⟩
    obtain ⟨bound, valid, encoded⟩ := decode_sound (s 2) capacity active formula decoded
    cases active with
    | zero =>
      have word : s 2 = formula.encode capacity 0 := encoded.symm
      have rank : (NativeHeader.parsedState (s 2)).count = 0 := by rw [word, NativeParser.header_encode capacity 0 bound formula]
      cases label : s 3 with
      | nil =>
        have flag : NativeEvaluation.verdict ((checkedStream (O := Symbol)).eval s) = true := by
          rw [checkedStream_verdict]
          simp [rank, label, validLabel, decoded]
        have buffer := checkedStream_zero_buffer (O := Symbol) capacity formula valid s word label
        calc
          streamOutput s = formula.encode capacity 0 := by simp [streamOutput, flag, buffer]
          _ = wordReduce (s 2) [] := by simpa [wordReduce, decoded] using encoded
      | cons head tail =>
        have flag : NativeEvaluation.verdict ((checkedStream (O := Symbol)).eval s) = false := by
          rw [checkedStream_verdict]
          simp [rank, label, validLabel]
        simp [streamOutput, flag, wordReduce, decoded, label]
    | succ active =>
      have word : s 2 = formula.encode capacity (active + 1) := encoded.symm
      have rank : (NativeHeader.parsedState (s 2)).count = active + 1 := by rw [word, NativeParser.header_encode capacity (active + 1) bound formula]
      cases labelBit : labelValue (s 3) with
      | none =>
        have flag : NativeEvaluation.verdict ((checkedStream (O := Symbol)).eval s) = false := by
          rw [checkedStream_verdict]
          simp [rank, validLabel, labelBit]
        simp [streamOutput, flag, wordReduce, decoded, labelBit]
      | some bit =>
        have label := labelValue_some (s 3) bit labelBit
        have flag : NativeEvaluation.verdict ((checkedStream (O := Symbol)).eval s) = true := by
          rw [checkedStream_verdict]
          simp [rank, validLabel, labelBit, decoded]
        have buffer := checkedStream_bit_buffer (O := Symbol) bit bound formula valid s word label
        calc
          streamOutput s = (formula.substitute (active + 1) bit).encode capacity active := by simp [streamOutput, flag, buffer]
          _ = wordReduce (s 2) (s 3) := by simp [wordReduce, decoded, labelBit]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
