import ComplexityOfGenerators.Examples.SATNative.SubstitutionReady
import ComplexityOfGenerators.Examples.SATNative.SubstitutionZero

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] bodyTransform tailSetup prepareStream selectLabel checkedStream

theorem selectLabel_zero_buffer {O : Type} (capacity : ℕ) (formula : Formula) (valid : formula.valid 0) (s : Store)
    (represented : Represents capacity 0 ⟨formula.bodyWord capacity, false, false, true⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length) (label : s 3 = []) :
    (selectLabel (O := O)).eval s 21 = (formula.encode capacity 0).reverse := by
  have transformed := bodyTransform_formula (O := O) false (Nat.zero_le capacity) formula valid true s represented enough
  have output := transformed.2
  rw [formula_substitute_zero false formula valid] at output
  simpa [selectLabel, Routine.branch, represented.2.2.1, label] using output

theorem selectLabel_bit_buffer {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active + 1 ≤ capacity)
    (formula : Formula) (valid : formula.valid (active + 1)) (s : Store)
    (represented : Represents capacity (active + 1) ⟨formula.bodyWord capacity, false, false, true⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length) (label : s 3 = [bitSymbol bit]) :
    (selectLabel (O := O)).eval s 21 = ((formula.substitute (active + 1) bit).encode capacity active).reverse := by
  let prepared := (tailSetup (O := O)).eval s
  have rep := tailSetup_represents (O := O) capacity (active + 1) _ s represented
  have clock : prepared 16 = s 16 := by simp [prepared, tailSetup_eval]
  have clockEnough : NativeBody.tokenCount formula ≤ (prepared 16).length := by rw [clock]; exact enough
  have transformed := bodyTransform_formula (O := O) bit bound formula valid true prepared rep clockEnough
  have empty : prepared 22 = [] := by simp [prepared, tailSetup_eval, label]
  have count := represented.2.2.1
  cases bit <;>
    simpa [selectLabel, Routine.branch, count, label, bitSymbol, List.replicate_succ,
      checkLabel, Routine.seq, show (tailSetup (O := O)).eval s = prepared by rfl, empty] using transformed.2

theorem checkedStream_zero_buffer {O : Type} (capacity : ℕ) (formula : Formula) (valid : formula.valid 0)
    (s : Store) (word : s 2 = formula.encode capacity 0) (label : s 3 = []) :
    (checkedStream (O := O)).eval s 21 = (formula.encode capacity 0).reverse := by
  rw [checkedStream_eval]
  have properties := prepareStream_properties (O := O) s
  dsimp only at properties
  rw [word, NativeParser.header_encode capacity 0 (Nat.zero_le _) formula, NativeParser.capacity_encode] at properties
  apply selectLabel_zero_buffer capacity formula valid _ properties.1
  · rw [properties.2.1]
    exact NativeBody.tokenCount_bound (Nat.zero_le _) formula valid
  · exact properties.2.2.trans label

theorem checkedStream_bit_buffer {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active + 1 ≤ capacity)
    (formula : Formula) (valid : formula.valid (active + 1)) (s : Store)
    (word : s 2 = formula.encode capacity (active + 1)) (label : s 3 = [bitSymbol bit]) :
    (checkedStream (O := O)).eval s 21 = ((formula.substitute (active + 1) bit).encode capacity active).reverse := by
  rw [checkedStream_eval]
  have properties := prepareStream_properties (O := O) s
  dsimp only at properties
  rw [word, NativeParser.header_encode capacity (active + 1) bound formula, NativeParser.capacity_encode] at properties
  apply selectLabel_bit_buffer bit bound formula valid _ properties.1
  · rw [properties.2.1]
    exact NativeBody.tokenCount_bound bound formula valid
  · exact properties.2.2.trans label

theorem labelValue_some (label : List Symbol) (bit : Bool) (encoded : labelValue label = some bit) :
    label = [bitSymbol bit] := by
  cases label with
  | nil => simp [labelValue] at encoded
  | cons head tail =>
    cases tail with
    | nil => cases head <;> cases bit <;> simp [labelValue, bitSymbol] at encoded ⊢
    | cons next rest => cases head <;> simp [labelValue] at encoded

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
