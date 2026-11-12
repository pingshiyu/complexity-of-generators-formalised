import ComplexityOfGenerators.Simulation.UnionGenerator.Views
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

/-! Bounded native concatenation samples every possible split. The first
successful pair is retained; a selector may replace it at each later split. -/
set_option maxHeartbeats 1600000

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

abbrev Cell := UnionGenerator.Cell G H
abbrev Store := Local.Store (Cell G H) 35
abbrev Controller := WordStack.Routine (Cell G H) α 35

def pairValue (left right : Option (List α)) : Option (List α) :=
  left.bind fun x => right.map fun y => x ++ y

def offer (previous candidate : Option (List α)) (replace : Bool) : Option (List α) :=
  if previous.isNone then candidate else if replace then candidate.or previous else previous

def next (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n j : ℕ)
    (p : Option (List α) × BitString) : Option (List α) × BitString :=
  let left := UnionGenerator.sourceValue G leftTime j (p.2.take (leftSeed j))
  let right := UnionGenerator.sourceValue H rightTime (n - j)
    ((p.2.drop (leftSeed j)).take (rightSeed (n - j)))
  let tail := p.2.drop (leftSeed j + rightSeed (n - j))
  (offer p.1 (pairValue left right) (tail.head? == some true), tail.drop 1)

def algorithm (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ)
    (bits : BitString) : Option (List α) :=
  ((List.range (n + 1)).foldl (fun p j => next G H leftSeed leftTime rightSeed rightTime n j p)
    (none, bits)).1

def save : Controller G H :=
  (WordStack.Routine.assign 26 31 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.copy 25 31 33 (by decide) (by decide) (by decide) id).seq
    (UnionGenerator.flag G H 32 true))

def offerStored : Controller G H :=
  WordStack.Routine.branch 27 fun left => if left.isNone then WordStack.Routine.skip else
  WordStack.Routine.branch 28 fun right => if right.isNone then WordStack.Routine.skip else
  WordStack.Routine.branch 32 fun found => if found.isNone then save G H else
  WordStack.Routine.branch 17 fun coin => match coin with
    | some (.bit true) => save G H
    | _ => WordStack.Routine.skip

def advance : Controller G H :=
  (WordStack.Routine.ofLocal (Local.pop 17)).seq
  ((WordStack.Routine.ofLocal (Local.push 23 .unit)).seq (WordStack.Routine.ofLocal (Local.pop 24)))

def reset : Controller G H :=
  (WordStack.Routine.clear 25).seq
  ((WordStack.Routine.clear 26).seq
  ((UnionGenerator.flag G H 27 false).seq (UnionGenerator.flag G H 28 false)))

noncomputable def splitStep (leftSeed leftTime rightSeed rightTime : PolynomialBound) : Controller G H :=
  (reset G H).seq
  ((WordStack.Routine.assign 23 13 33 (by decide) (by decide) (by decide) id).seq
  ((UnionGenerator.leftTrial G H leftSeed leftTime).seq
  ((UnionGenerator.leftFinish G H).seq
  ((WordStack.Routine.assign 24 13 33 (by decide) (by decide) (by decide) id).seq
  ((UnionGenerator.rightTrial G H rightSeed rightTime).seq
  ((UnionGenerator.rightFinish G H).seq
  ((offerStored G H).seq (advance G H))))))))

theorem sourceTrial_fixes_clock {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell G H) (decode : Cell G H → Source.Symbol M)
    (f g b : Cell G H → Cell G H) (seed time : PolynomialBound) :
    (BoundedSource.sourceTrial (Symbol.unit : Cell G H) Symbol.bit M encode decode f g b seed time).Fixes 30 := by
  intro s
  simpa [BoundedSource.trialPrepared] using
    BoundedSource.sourceTrial_outside (O := α) (Symbol.unit : Cell G H) Symbol.bit M encode decode f g b
      seed time s 30 (by decide) (by decide)

theorem flag_fixes_clock (reg : Fin 35) (different : reg ≠ 30) (value : Bool) :
    (UnionGenerator.flag G H reg value).Fixes 30 := by
  intro s
  simp [UnionGenerator.flag_eval, different.symm]

theorem finish_fixes_clock (left : Bool) :
    (if left then UnionGenerator.leftFinish G H else UnionGenerator.rightFinish G H).Fixes 30 := by
  cases left <;> intro s <;>
    simp only [Bool.false_eq_true, ↓reduceIte, UnionGenerator.leftFinish, UnionGenerator.rightFinish,
      WordStack.Routine.branch] <;>
    split <;> simp [WordStack.Routine.seq, UnionGenerator.takeOutput_eval, UnionGenerator.flag_eval,
      WordStack.Routine.clear]

theorem save_fixes_clock : (save G H).Fixes 30 := by
  intro s
  simp [save, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.copy,
    UnionGenerator.flag_eval]

theorem offerStored_fixes_clock : (offerStored G H).Fixes 30 := by
  apply WordStack.Routine.Fixes.branch
  intro left
  split
  · exact WordStack.Routine.fixes_skip 30
  · apply WordStack.Routine.Fixes.branch
    intro right
    split
    · exact WordStack.Routine.fixes_skip 30
    · apply WordStack.Routine.Fixes.branch
      intro found
      split
      · exact save_fixes_clock G H
      · apply WordStack.Routine.Fixes.branch
        intro coin
        split
        · exact save_fixes_clock G H
        · exact WordStack.Routine.fixes_skip 30

theorem advance_fixes_clock : (advance G H).Fixes 30 := by
  intro s
  simp [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push]

theorem reset_fixes_clock : (reset G H).Fixes 30 := by
  intro s
  simp [reset, WordStack.Routine.seq, WordStack.Routine.clear, UnionGenerator.flag_eval]

theorem splitStep_fixes_clock (leftSeed leftTime rightSeed rightTime : PolynomialBound) :
    (splitStep G H leftSeed leftTime rightSeed rightTime).Fixes 30 :=
  (reset_fixes_clock G H).seq
  ((WordStack.Routine.fixes_assign 23 13 33 (by decide) (by decide) (by decide) id 30 (by decide) (by decide)).seq
  ((sourceTrial_fixes_clock G H G _ _ _ _ _ leftSeed leftTime).seq
  ((finish_fixes_clock G H true).seq
  ((WordStack.Routine.fixes_assign 24 13 33 (by decide) (by decide) (by decide) id 30 (by decide) (by decide)).seq
  ((sourceTrial_fixes_clock G H H _ _ _ _ _ rightSeed rightTime).seq
  ((finish_fixes_clock G H false).seq
  ((offerStored_fixes_clock G H).seq (advance_fixes_clock G H))))))))

def setup : Controller G H :=
  (WordStack.Routine.assign 13 22 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.assign 13 24 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.assign 13 30 33 (by decide) (by decide) (by decide) id).seq
  (WordStack.Routine.ofLocal (Local.push 30 .unit))))

noncomputable def body (leftSeed leftTime rightSeed rightTime : PolynomialBound) : Controller G H :=
  (setup G H).seq
  ((WordStack.Routine.iterate 30 (splitStep G H leftSeed leftTime rightSeed rightTime)
    (splitStep_fixes_clock G H leftSeed leftTime rightSeed rightTime)).seq
  (WordStack.Routine.assign 22 13 33 (by decide) (by decide) (by decide) id))

def finish : Command (Cell G H) α 35 :=
  .branch 32 fun found => if found.1.isSome then
    Command.emitWord 31 (UnionGenerator.outputLetter G H) else .drain

noncomputable def command (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) :
    Command (Cell G H) α 35 :=
  (BoundedSource.prepareCommand .unit Symbol.bit seed).seq
    ((body G H leftSeed leftTime rightSeed rightTime).command.seq (finish G H))

end ComplexityOfGenerators.Simulation.ConcatenationGenerator
