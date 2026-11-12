import ComplexityOfGenerators.Examples.SATNative.InverseNative.Step
import ComplexityOfGenerators.Examples.SATNative.InverseNative.LiteralBounds
import ComplexityOfGenerators.Examples.SATNative.EvaluationStep

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
open Simulation.WordStack NativeBody
set_option backward.isDefEq.respectTransparency false

private theorem stackBound_mono {s : Store} {small large : ℕ} (sizes : stackBound small s)
    (bound : small ≤ large) : stackBound large s := fun j => (sizes j).trans bound

private theorem pushOutput_bound (symbol : Symbol) (s : Store) (budget capacity : ℕ)
    (sizes : stackBound budget s) :
    stackBound (budget+capacity+1) (Function.update s 21 (symbol::s 21)) := by
  exact StoreBound.update (stackBound_mono sizes (by omega : budget ≤ budget+capacity+1)) 21 _
    (by have := sizes 21; simp only [List.length_cons]; omega)

theorem inverseStep_bound {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (more : active+1 ≤ capacity) :
    stackBound (budget+capacity+1) ((inverseStep (O := O) bit).eval s) := by
  have wordReg := represented.1
  have insideReg := represented.2.2.2.2.1
  have parsed := bodyStep_bound (O := O) capacity active state s represented budget positive sizes cap (more.trans cap)
  have parsedRep := bodyStep_represents (O := O) capacity active state s represented
  cases word : state.word with
  | nil => simpa [inverseStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval] using
      stackBound_mono sizes (by omega : budget ≤ budget+capacity+1)
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause
      · simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushOutput_bound .openClause _ budget capacity parsed
      · simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.eval] using
          stackBound_mono parsed (by omega : budget ≤ budget+capacity+1)
    | true =>
      by_cases close : tag = .closeClause
      · simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushOutput_bound .closeClause _ budget capacity parsed
      · have details := NativeEvaluation.bodyStep_literal_details (O := O) capacity active state s represented tag rest word inside close
        dsimp only at details
        have capReg := parsedRep.2.1
        have within : (((bodyStep (O := O)).eval s) 5).length ≤ (((bodyStep (O := O)).eval s) 4).length := by
          rw [details.1, capReg]
          simp only [List.length_replicate]
          exact NativeLiteral.field_count capacity state.word
        have fresh : (((bodyStep (O := O)).eval s) 10).length + 1 ≤ (((bodyStep (O := O)).eval s) 4).length := by
          rw [parsedRep.2.2.1, capReg]
          simpa only [List.length_replicate] using more
        have emitted := liftLiteral_bound (O := O) bit _ budget positive parsed within fresh
        rw [capReg, List.length_replicate] at emitted
        simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, close, Routine.seq] using emitted

theorem inverseStep_cost {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (more : active+1 ≤ capacity) :
    (inverseStep (O := O) bit).cost s ≤ (stepConstant+300)*(budget+1) := by
  have wordReg := represented.1
  have insideReg := represented.2.2.2.2.1
  have parsed := bodyStep_bound (O := O) capacity active state s represented budget positive sizes cap (more.trans cap)
  have parseCost := bodyStep_cost (O := O) capacity active state s represented budget positive sizes cap (more.trans cap)
  have parsedRep := bodyStep_represents (O := O) capacity active state s represented
  have fresh : (((bodyStep (O := O)).eval s) 10).length + 1 ≤ budget := by
    rw [parsedRep.2.2.1]
    simpa only [List.length_replicate] using more.trans cap
  have emitCost := liftLiteral_cost (O := O) bit _ budget positive parsed fresh
  cases word : state.word with
  | nil =>
    simp only [inverseStep, Routine.branch, wordReg, word, List.head?_nil, Routine.skip, Routine.ofLocal, Local.ticks]
    nlinarith
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause <;>
        simp only [inverseStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          Bool.false_eq_true, ite_false, List.head?_nil, Option.isSome_none, opening, ite_true,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.push, Local.ticks] <;> nlinarith
    | true =>
      by_cases close : tag = .closeClause <;>
        simp only [inverseStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, ite_false, Routine.seq, Routine.ofLocal, Local.push, Local.ticks] <;> nlinarith

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
