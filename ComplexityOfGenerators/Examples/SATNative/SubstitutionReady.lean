import ComplexityOfGenerators.Examples.SATNative.SubstitutionLabels

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

noncomputable def prepareStream {O : Type} : Routine Symbol O 32 := NativeParser.header.seq NativeParser.bodySetup

noncomputable def checkedStream {O : Type} : Routine Symbol O 32 := prepareStream.seq selectLabel

attribute [local irreducible] NativeParser.header NativeParser.bodySetup selectLabel prepareStream

theorem prepareStream_eval {O : Type} (s : Store) :
    (prepareStream (O := O)).eval s = (NativeParser.bodySetup (O := O)).eval ((NativeParser.header (O := O)).eval s) := by
  simp only [prepareStream, Routine.seq]

theorem checkedStream_eval {O : Type} (s : Store) :
    (checkedStream (O := O)).eval s = (selectLabel (O := O)).eval ((prepareStream (O := O)).eval s) := by
  simp only [checkedStream, Routine.seq]

theorem prepareStream_properties {O : Type} (s : Store) :
    let prepared := (prepareStream (O := O)).eval s
    Represents (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count
      ⟨(NativeHeader.parsedState (s 2)).word, false, false, (NativeHeader.parsedState (s 2)).valid⟩ prepared ∧
    (prepared 16).length = (NativeHeader.parsedState (s 2)).word.length ∧ prepared 3 = s 3 := by
  dsimp only
  rw [prepareStream_eval]
  have fields := NativeParser.header_fields (O := O) s
  dsimp only at fields
  have ready := NativeParser.bodySetup_represents (O := O) ((NativeParser.header (O := O)).eval s)
    (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (NativeHeader.parsedState (s 2)).word
    (NativeHeader.parsedState (s 2)).valid fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
  refine ⟨ready.1, ready.2, ?_⟩
  rw [NativeEvaluation.bodySetup_certificate, NativeEvaluation.header_certificate]

theorem checkedStream_verdict {O : Type} (s : Store) :
    NativeEvaluation.verdict ((checkedStream (O := O)).eval s) =
      if validLabel (NativeHeader.parsedState (s 2)).count (s 3) then (decode (s 2)).isSome else false := by
  rw [checkedStream_eval]
  have properties := prepareStream_properties (O := O) s
  dsimp only at properties
  have signal := selectLabel_verdict (O := O) _ _ _ _ properties.1
  rw [properties.2.1, properties.2.2] at signal
  have codec : NativeBody.accepts
      ((NativeBody.step (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count)^[(NativeHeader.parsedState (s 2)).word.length]
        ⟨(NativeHeader.parsedState (s 2)).word, false, false, (NativeHeader.parsedState (s 2)).valid⟩) =
      (decode (s 2)).isSome := NativeParser.accepted_eq_decode (s 2)
  simpa only [codec] using signal

@[simp] theorem prepareStream_randomFree {O : Type} : Command.RandomFree (prepareStream (O := O)).command := by
  simp [prepareStream, NativeParser.bodySetup]

@[simp] theorem checkedStream_randomFree {O : Type} : Command.RandomFree (checkedStream (O := O)).command := by simp [checkedStream]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
