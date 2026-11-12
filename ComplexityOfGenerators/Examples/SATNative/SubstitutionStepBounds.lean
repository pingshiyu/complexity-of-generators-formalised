import ComplexityOfGenerators.Examples.SATNative.SubstitutionFrames
import ComplexityOfGenerators.Examples.SATNative.SubstitutionHeaderBounds
import ComplexityOfGenerators.Examples.SATNative.EvaluationStep

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
open Simulation.WordStack NativeBody
set_option backward.isDefEq.respectTransparency false

private theorem stackBound_mono {s : Store} {small large : ℕ} (sizes : stackBound small s)
    (bound : small ≤ large) : stackBound large s := fun j => (sizes j).trans bound

theorem substituteLiteral_bound {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (within : (s 5).length ≤ (s 4).length) :
    stackBound (budget+(s 4).length+1) ((substituteLiteral (O := O) bit).eval s) := by
  let after := (rewriteLiteral (O := O) bit).eval s
  have afterBound := rewriteLiteral_bound (O := O) bit s budget positive sizes
  have cap : after 4 = s 4 := rewriteLiteral_frame bit s 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have index := rewriteLiteral_index_length (O := O) bit s
  have before : (after 5).length ≤ (after 4).length := by rw [cap]; exact index.trans within
  change stackBound (budget+(s 4).length+1) ((emitLiteral (O := O)).eval after)
  simpa only [cap] using emitLiteral_bound (O := O) after budget afterBound before

theorem substituteLiteral_cost {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) :
    (substituteLiteral (O := O) bit).cost s ≤ 260*(budget+1) := by
  have first := rewriteLiteral_cost (O := O) bit s budget positive sizes
  have after := rewriteLiteral_bound (O := O) bit s budget positive sizes
  have second := emitLiteral_cost (O := O) _ budget after
  change (rewriteLiteral bit).cost s+1+(emitLiteral (O := O)).cost ((rewriteLiteral bit).eval s) ≤ _
  omega

private theorem pushOutput_bound (symbol : Symbol) (s : Store) (budget capacity : ℕ)
    (sizes : stackBound budget s) :
    stackBound (budget+capacity+1) (Function.update s 21 (symbol::s 21)) := by
  exact StoreBound.update (stackBound_mono sizes (by omega : budget ≤ budget+capacity+1)) 21 _
    (by have := sizes 21; simp only [List.length_cons]; omega)

theorem substitutionStep_bound {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active+1 ≤ budget) :
    stackBound (budget+capacity+1) ((substitutionStep (O := O) bit).eval s) := by
  have wordReg := represented.1
  have insideReg := represented.2.2.2.2.1
  have parsed := bodyStep_bound (O := O) capacity active state s represented budget positive sizes cap count
  have parsedRep := bodyStep_represents (O := O) capacity active state s represented
  cases word : state.word with
  | nil => simpa [substitutionStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval] using
      stackBound_mono sizes (by omega : budget ≤ budget+capacity+1)
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause
      · simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushOutput_bound .openClause _ budget capacity parsed
      · simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.eval] using
          stackBound_mono parsed (by omega : budget ≤ budget+capacity+1)
    | true =>
      by_cases close : tag = .closeClause
      · simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushOutput_bound .closeClause _ budget capacity parsed
      · have details := NativeEvaluation.bodyStep_literal_details (O := O) capacity active state s represented tag rest word inside close
        dsimp only at details
        have capReg := parsedRep.2.1
        have within : (((bodyStep (O := O)).eval s) 5).length ≤ (((bodyStep (O := O)).eval s) 4).length := by
          rw [details.1, capReg]
          simp only [List.length_replicate]
          exact NativeLiteral.field_count capacity state.word
        have emitted := substituteLiteral_bound (O := O) bit _ budget positive parsed within
        rw [capReg, List.length_replicate] at emitted
        simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, close, Routine.seq] using emitted

theorem substitutionStep_cost {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active+1 ≤ budget) :
    (substitutionStep (O := O) bit).cost s ≤ (stepConstant+300)*(budget+1) := by
  have wordReg := represented.1
  have insideReg := represented.2.2.2.2.1
  have parsed := bodyStep_bound (O := O) capacity active state s represented budget positive sizes cap count
  have parseCost := bodyStep_cost (O := O) capacity active state s represented budget positive sizes cap count
  have emitCost := substituteLiteral_cost (O := O) bit _ budget positive parsed
  cases word : state.word with
  | nil =>
    simp only [substitutionStep, Routine.branch, wordReg, word, List.head?_nil, Routine.skip, Routine.ofLocal, Local.ticks]
    nlinarith
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause <;>
        simp only [substitutionStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          Bool.false_eq_true, ite_false, List.head?_nil, Option.isSome_none, opening, ite_true,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.push, Local.ticks] <;> nlinarith
    | true =>
      by_cases close : tag = .closeClause <;>
        simp only [substitutionStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, ite_false, Routine.seq, Routine.ofLocal, Local.push, Local.ticks] <;> nlinarith

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
