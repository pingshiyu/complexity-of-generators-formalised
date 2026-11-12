import ComplexityOfGenerators.Examples.SATNative.VerifierModel
import ComplexityOfGenerators.Examples.SATNative.CertificateBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody
open NativeAssignment

set_option backward.isDefEq.respectTransparency false

noncomputable def prepareEvaluation {O : Type} : Routine Symbol O 32 :=
  NativeParser.header.seq (NativeParser.bodySetup.seq ((Routine.clear 20).seq certificateCheck))

set_option maxHeartbeats 1000000 in
theorem prepareEvaluation_eval {O : Type} (s : Store) :
    (prepareEvaluation (O := O)).eval s = (certificateCheck (O := O)).eval
      (Function.update ((NativeParser.bodySetup (O := O)).eval ((NativeParser.header (O := O)).eval s)) 20 []) := by
  simp only [prepareEvaluation, Routine.seq, Routine.clear]

def readyState (word : List Symbol) : State :=
  initial (NativeHeader.parsedState word).word (NativeHeader.parsedState word).valid

theorem header_certificate {O : Type} (s : Store) : (NativeParser.header (O := O)).eval s 3 = s 3 := by
  have here := Routine.rename_eval_here (NativeHeader.headerRoutine (O := O)) subslots s 3
  rw [NativeHeader.headerRoutine_eval] at here
  simpa [NativeParser.header, subslots, NativeHeader.encoded, NativeHeader.scaffold, Function.comp_def] using here

theorem bodySetup_certificate {O : Type} (s : Store) : (NativeParser.bodySetup (O := O)).eval s 3 = s 3 := by
  simp [NativeParser.bodySetup, Routine.seq, Routine.assign_eval, Routine.clearMany_eval]

theorem certificateCheck_represents {O : Type} (capacity active : ℕ) (certificate : List Symbol)
    (state : State) (s : Store) (represented : Represents capacity active certificate state s) :
    Represents capacity active certificate state ((certificateCheck (O := O)).eval s) := by
  rcases represented with ⟨parserRep, cert, truth⟩
  rcases parserRep with ⟨word, cap, count, valid, inside, seen⟩
  have frame (j : Fin 32) (a : j ≠ 9) (b : j ≠ 22) (c : j ≠ 23) (d : j ≠ 24) (e : j ≠ 25) (f : j ≠ 27) :=
    certificateCheck_frame (O := O) s j a b c d e f
  simp [Represents, NativeBody.Represents, frame, word, cap, count, valid, inside, seen, cert, truth]

set_option maxHeartbeats 800000 in
theorem prepareEvaluation_properties {O : Type} (s : Store) :
    let ready := (prepareEvaluation (O := O)).eval s
    Represents (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (s 3) (readyState (s 2)) ready ∧
      (ready 16).length = (NativeHeader.parsedState (s 2)).word.length ∧
      ready 27 = (if (s 3).length = (NativeHeader.parsedState (s 2)).count ∧ Binary (s 3) then [.one] else []) := by
  dsimp only
  rw [prepareEvaluation_eval]
  let first := (NativeParser.header (O := O)).eval s
  let second := (NativeParser.bodySetup (O := O)).eval first
  let third := Function.update second 20 ([] : List Symbol)
  have fields := NativeParser.header_fields (O := O) s
  dsimp only at fields
  obtain ⟨parserRep, clock⟩ := NativeParser.bodySetup_represents (O := O) first
    (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (NativeHeader.parsedState (s 2)).word
    (NativeHeader.parsedState (s 2)).valid fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
  have thirdRep : Represents (readOnes (s 2)).1 (NativeHeader.parsedState (s 2)).count (s 3) (readyState (s 2)) third := by
    refine ⟨clearTruth_parserFrame _ _ _ _ parserRep, ?_, ?_⟩
    · simp [third, second, bodySetup_certificate, first, header_certificate]
    · simp [third, readyState, initial]
  have represented := certificateCheck_represents (O := O) _ _ _ _ third thirdRep
  have clockFrame := certificateCheck_frame (O := O) third 16 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have validity := certificateCheck_result (O := O) third
  have thirdWord : third 3 = s 3 := thirdRep.2.1
  have thirdCount : third 10 = List.replicate (NativeHeader.parsedState (s 2)).count .one := thirdRep.1.2.2.1
  refine ⟨represented, ?_, ?_⟩
  · change (((certificateCheck (O := O)).eval third) 16).length = _
    rw [clockFrame]
    simpa [third] using clock
  · change (certificateCheck (O := O)).eval third 27 = _
    simpa only [thirdWord, thirdCount, List.length_replicate] using validity

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
