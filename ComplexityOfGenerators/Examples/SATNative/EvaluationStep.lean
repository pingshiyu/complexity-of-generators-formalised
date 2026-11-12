import ComplexityOfGenerators.Examples.SATNative.EvaluationRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem bodyStep_literal_details {O : Type} (capacity active : ℕ) (state : NativeBody.State) (s : Store)
    (represented : NativeBody.Represents capacity active state s) (tag : Symbol) (rest : List Symbol)
    (word : state.word = tag :: rest) (inside : state.inside = true) (close : tag ≠ .closeClause) :
    let output := (bodyStep (O := O)).eval s
    output 5 = List.replicate (NativeLiteral.fieldState capacity state.word).count .one ∧
      output 11 = state.word.head?.toList := by
  have details := literal_details (O := O) capacity active state s represented
  dsimp only at details ⊢
  rcases represented with ⟨wordReg, _, _, _, insideReg, _⟩
  simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, close,
    Routine.seq, Routine.ofLocal, Local.eval_write] using details.2

theorem clearTruth_parserFrame (capacity active : ℕ) (state : NativeBody.State) (s : Store)
    (represented : NativeBody.Represents capacity active state s) :
    NativeBody.Represents capacity active state (Function.update s 20 []) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  simp [NativeBody.Represents, word, cap, count, valid, inside, seen]

set_option maxHeartbeats 800000 in
theorem evaluationStep_represents {O : Type} (capacity active : ℕ) (certificate : List Symbol)
    (state : State) (s : Store) (represented : Represents capacity active certificate state s) :
    Represents capacity active certificate (step capacity active certificate state) ((evaluationStep (O := O)).eval s) := by
  rcases represented with ⟨parserRep, certificateReg, truthReg⟩
  have parserSaved := parserRep
  rcases parserSaved with ⟨wordReg, capReg, countReg, validReg, insideReg, seenReg⟩
  have parsedRep := NativeBody.bodyStep_represents (O := O) capacity active state.parserState s parserRep
  have parsedCert := bodyStep_certificate (O := O) capacity active state.parserState s parserRep
  have parsedTruth := bodyStep_truthFrame (O := O) s
  cases word : state.parserState.word with
  | nil =>
    simpa [Represents, evaluationStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal,
      Local.eval, step] using And.intro parserRep (And.intro certificateReg truthReg)
  | cons tag rest =>
    cases inside : state.parserState.inside with
    | false =>
      have fixedRep := clearTruth_parserFrame capacity active _ _ parsedRep
      refine ⟨?_, ?_, ?_⟩
      · by_cases opening : tag = .openClause <;>
          simpa [evaluationStep, Routine.branch, wordReg, word, insideReg, inside,
            Routine.seq, Routine.clear, step, NativeBody.step, opening] using fixedRep
      · simp [evaluationStep, Routine.branch, wordReg, word, insideReg, inside,
          Routine.seq, Routine.clear, parsedCert, certificateReg]
      · by_cases opening : tag = .openClause <;>
          simp [evaluationStep, Routine.branch, wordReg, word, insideReg, inside,
            Routine.seq, Routine.clear, step, opening]
    | true =>
      by_cases close : tag = .closeClause
      · subst tag
        rcases parsedRep with ⟨nextWord, nextCap, nextCount, nextValid, nextInside, nextSeen⟩
        cases truth : state.clauseValue <;> cases good : state.parserState.valid <;>
          cases seen : state.parserState.nonempty <;>
            simp [Represents, NativeBody.Represents, evaluationStep, Routine.branch, wordReg, word, insideReg, inside,
              Routine.seq, Routine.ofLocal, closeTruthCode, Local.eval, Local.pop, Action.apply,
              parsedTruth, truthReg, truth, nextWord, nextCap, nextCount, nextValid, nextInside, nextSeen,
              parsedCert, certificateReg, step, NativeBody.step, good, seen]
      · let parsed : Store := (bodyStep (O := O)).eval s
        let valued : Store := (NativeAssignment.literalValue (O := O)).eval parsed
        have valuedRep := literalValue_parserFrame (O := O) capacity active _ parsed parsedRep
        have valuedCert : valued 3 = certificate := by
          change (NativeAssignment.literalValue (O := O)).eval parsed 3 = certificate
          rw [NativeAssignment.literalValue_frame (O := O) parsed 3 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)]
          exact parsedCert.trans certificateReg
        have valuedTruth : valued 20 = if state.clauseValue then [.one] else [] := by
          change (NativeAssignment.literalValue (O := O)).eval parsed 20 = _
          rw [NativeAssignment.literalValue_frame (O := O) parsed 20 (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)]
          exact parsedTruth.trans truthReg
        have details := bodyStep_literal_details (O := O) capacity active state.parserState s parserRep tag rest word inside close
        have selected : valued 26 = if literalTruth active certificate state.parserState.word capacity then [.one] else [] := by
          change (NativeAssignment.literalValue (O := O)).eval parsed 26 = _
          rw [NativeAssignment.literalValue_result]
          have parsedCount : parsed 10 = List.replicate active .one := parsedRep.2.2.1
          have parsedIndex : parsed 5 = List.replicate (NativeLiteral.fieldState capacity state.parserState.word).count .one := details.1
          have parsedTag : parsed 11 = state.parserState.word.head?.toList := details.2
          have parsedCertificate : parsed 3 = certificate := parsedCert.trans certificateReg
          simp [literalTruth, parsedIndex, parsedTag, parsedCertificate, parsedCount]
        rcases valuedRep with ⟨nextWord, nextCap, nextCount, nextValid, nextInside, nextSeen⟩
        change valued 2 = _ at nextWord
        change valued 4 = _ at nextCap
        change valued 10 = _ at nextCount
        change valued 6 = _ at nextValid
        change valued 17 = _ at nextInside
        change valued 18 = _ at nextSeen
        cases old : state.clauseValue <;> cases new : literalTruth active certificate state.parserState.word capacity
        all_goals have newHead := new
        all_goals rw [word] at newHead
        all_goals simp [Represents, NativeBody.Represents, evaluationStep, Routine.branch, wordReg, word, insideReg, inside, close,
            Routine.seq, Routine.ofLocal, accumulateCode, Local.eval, Local.write, Local.pop, Local.push, Action.apply,
            show (NativeAssignment.literalValue (O := O)).eval ((bodyStep (O := O)).eval s) = valued by rfl,
            selected, valuedTruth, valuedCert, nextWord, nextCap, nextCount, nextValid, nextInside, nextSeen,
            step, NativeBody.step, old, newHead]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
