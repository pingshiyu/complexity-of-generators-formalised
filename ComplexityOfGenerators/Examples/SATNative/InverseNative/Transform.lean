import ComplexityOfGenerators.Examples.SATNative.InverseNative.Complete
import ComplexityOfGenerators.Examples.SATNative.SubstitutionReady

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeBody
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] NativeHeader.headerRoutine NativeParser.header NativeParser.bodySetup
  NativeSubstitution.prepareStream

noncomputable def bodyTransform {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  emitHeader.seq (inverseRoutine bit)

theorem emitHeader_parserFrame {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state ((emitHeader (O := O)).eval s) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  have frame (j : Fin 32) (a : j ≠ 9) (b : j ≠ 21) (c : j ≠ 22) (d : j ≠ 23) (e : j ≠ 24) (f : j ≠ 25) :=
    emitHeader_frame (O := O) s j a b c d e f
  simp [Represents, frame, word, cap, count, valid, inside, seen]

theorem bodyTransform_formula {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨formula.bodyWord capacity, false, false, enabled⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (bodyTransform (O := O) bit).eval s
    Represents capacity active ⟨[], false, false, enabled⟩ output ∧
      output 31 = (choices.drop formula.occurrences).map bitSymbol ∧
      output 21 = ((formula.lift active bit (choiceRows formula choices)).encode capacity (active+1)).reverse := by
  dsimp only [bodyTransform, Routine.seq]
  let prepared := (emitHeader (O := O)).eval s
  have preparedRep := emitHeader_parserFrame (O := O) capacity active _ s represented
  have clock : prepared 16 = s 16 := emitHeader_frame (O := O) s 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have clockEnough : NativeBody.tokenCount formula ≤ (prepared 16).length := by rw [clock]; exact enough
  have preparedMask : prepared 31 = choices.map bitSymbol :=
    (emitHeader_frame (O := O) s 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans mask
  have parsed := inverseRoutine_formula (O := O) bit bound formula valid enabled prepared preparedRep clockEnough choices preparedMask
  refine ⟨parsed.1, parsed.2.1, ?_⟩
  have initialBuffer : prepared 21 = (NativeSubstitution.headerWord capacity (active+1)).reverse := by
    have buffer := emitHeader_buffer (O := O) s
    simpa only [represented.2.1, represented.2.2.1, List.length_replicate] using buffer
  rw [parsed.2.2, initialBuffer, ← List.reverse_append, ← NativeSubstitution.encode_as_headerBody]

noncomputable def stream {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  NativeSubstitution.prepareStream.seq (bodyTransform bit)

theorem prepareStream_mask {O : Type} (s : Store) :
    (NativeSubstitution.prepareStream (O := O)).eval s 31 = s 31 := by
  rw [NativeSubstitution.prepareStream_eval]
  have header := Routine.rename_eval_frame (NativeHeader.headerRoutine (O := O)) NativeBody.subslots s 31
    (by intro j equal; have := congrArg (fun q : Fin 32 => q.val) equal; simp only [NativeBody.subslots_val] at this; omega)
  simpa [NativeParser.bodySetup, NativeParser.header, Routine.seq, Routine.assign_eval, Routine.clearMany_eval] using header

theorem stream_buffer {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (s : Store)
    (word : s 2 = formula.encode capacity active) (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    (stream (O := O) bit).eval s 21 =
      ((formula.lift active bit (choiceRows formula choices)).encode capacity (active+1)).reverse := by
  have properties := NativeSubstitution.prepareStream_properties (O := O) s
  dsimp only at properties
  rw [word, NativeParser.header_encode capacity active bound formula, NativeParser.capacity_encode] at properties
  have parsedMask : (NativeSubstitution.prepareStream (O := O)).eval s 31 = choices.map bitSymbol :=
    (prepareStream_mask (O := O) s).trans mask
  have result := bodyTransform_formula (O := O) bit bound formula valid true _ properties.1
    (by rw [properties.2.1]; exact NativeBody.tokenCount_bound bound formula valid) choices parsedMask
  exact result.2.2

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
