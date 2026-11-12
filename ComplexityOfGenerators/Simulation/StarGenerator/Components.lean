import ComplexityOfGenerators.Simulation.StarGenerator.Table
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Views

set_option maxHeartbeats 1200000

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

def advance : Controller G :=
  (WordStack.Routine.ofLocal (Local.pop 17)).seq (WordStack.Routine.ofLocal (Local.push 24 .unit))

def sourceSetup : Controller G :=
  (readEntry G).seq
  ((UnionGenerator.flag G G 27 false).seq
    (WordStack.Routine.assign 24 13 33 (by decide) (by decide) (by decide) id))

noncomputable def innerStep (seed time : PolynomialBound) : Controller G :=
  (sourceSetup G).seq
  ((UnionGenerator.leftTrial G G seed time).seq
  ((UnionGenerator.leftFinish G G).seq
  ((ConcatenationGenerator.offerStored G G).seq (advance G))))

theorem readEntry_fixes (j : Fin 35) (a : j ≠ 25) (b : j ≠ 26) (c : j ≠ 28) (d : j ≠ 34) :
    (readEntry G).Fixes j := by
  intro s
  simp [readEntry, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.branch,
    UnionGenerator.flag_eval, WordStack.Routine.ofLocal, Local.eval_pop,
    WordStack.Routine.transferWhile, WordStack.Routine.transfer, a, b, c, d]

theorem offerStored_fixes (j : Fin 35) (a : j ≠ 31) (b : j ≠ 32) (c : j ≠ 33) :
    (ConcatenationGenerator.offerStored G G).Fixes j := by
  intro s
  simp only [ConcatenationGenerator.offerStored, WordStack.Routine.branch]
  split <;> try rfl
  simp only [WordStack.Routine.branch]
  split <;> try rfl
  simp only [WordStack.Routine.branch]
  split
  · simp [ConcatenationGenerator.save_eval, a, b, c]
  · simp only [WordStack.Routine.branch]
    split <;> simp [ConcatenationGenerator.save_eval, WordStack.Routine.skip,
      WordStack.Routine.ofLocal, Local.eval, a, b, c]

theorem advance_fixes (j : Fin 35) (random : j ≠ 17) (index : j ≠ 24) : (advance G).Fixes j := by
  intro s
  simp [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal,
    Local.eval_pop, Local.eval_push, random, index]

theorem flag_fixes (reg j : Fin 35) (different : j ≠ reg) (value : Bool) :
    (UnionGenerator.flag G G reg value).Fixes j := by
  intro s
  simp [UnionGenerator.flag_eval, different]

theorem sourceSetup_fixes (j : Fin 35) (index : j ≠ 13) (left : j ≠ 25) (right : j ≠ 26)
    (leftFlag : j ≠ 27) (rightFlag : j ≠ 28) (scratch : j ≠ 33) (cursor : j ≠ 34) :
    (sourceSetup G).Fixes j :=
  (readEntry_fixes G j left right rightFlag cursor).seq
  ((flag_fixes G 27 j leftFlag false).seq
    (WordStack.Routine.fixes_assign 24 13 33 (by decide) (by decide) (by decide) id j index scratch))

theorem innerStep_fixes (seed time : PolynomialBound) (j : Fin 35) (which : j = 22 ∨ j = 30) :
    (innerStep G seed time).Fixes j := by
  have large : 22 ≤ j.val := by rcases which with rfl | rfl <;> decide
  have neq (r : Fin 35) (different : r ≠ 22 ∧ r ≠ 30) : j ≠ r := by
    rcases which with rfl | rfl <;> simp_all [ne_comm]
  apply (sourceSetup_fixes G j (neq 13 (by decide)) (neq 25 (by decide)) (neq 26 (by decide))
    (neq 27 (by decide)) (neq 28 (by decide)) (neq 33 (by decide)) (neq 34 (by decide))).seq
  apply (ConcatenationGenerator.sourceTrial_fixes_outer G G G Symbol.left (UnionGenerator.leftDecode G G)
    (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit G G) seed time j large).seq
  apply (ConcatenationGenerator.leftFinish_fixes_outer G G j large
    (neq 25 (by decide)) (neq 27 (by decide))).seq
  exact (offerStored_fixes G j (neq 31 (by decide)) (neq 32 (by decide)) (neq 33 (by decide))).seq
    (advance_fixes G j (neq 17 (by decide)) (neq 24 (by decide)))

def stageSetup : Controller G :=
  (WordStack.Routine.ofLocal (Local.push 23 .unit)).seq
  ((WordStack.Routine.assign 23 30 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.clear 24).seq
  ((WordStack.Routine.ofLocal (Local.push 24 .unit)).seq
  ((WordStack.Routine.clear 31).seq
  ((UnionGenerator.flag G G 32 false).seq
    (WordStack.Routine.assign 29 34 33 (by decide) (by decide) (by decide) id))))))

theorem stageSetup_fixes_clock : (stageSetup G).Fixes 22 := by
  intro s
  simp [stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
    WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval]

noncomputable def stageStep (seed time : PolynomialBound) : Controller G :=
  (stageSetup G).seq
  ((WordStack.Routine.iterate 30 (innerStep G seed time) (innerStep_fixes G seed time 30 (Or.inr rfl))).seq
    (appendEntry G))

theorem stageStep_fixes_clock (seed time : PolynomialBound) : (stageStep G seed time).Fixes 22 :=
  (stageSetup_fixes_clock G).seq
  ((WordStack.Routine.Fixes.iterate 30 (innerStep G seed time) (innerStep_fixes G seed time 30 (Or.inr rfl))
    22 (by decide) (innerStep_fixes G seed time 22 (Or.inl rfl))).seq
    (appendEntry_fixes G 22 (by decide) (by decide)))

def setup : Controller G :=
  (WordStack.Routine.assign 13 22 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.ofLocal (Local.push 29 (someMarker G))).seq (UnionGenerator.flag G G 32 true))

noncomputable def body (seed time : PolynomialBound) : Controller G :=
  (setup G).seq (WordStack.Routine.iterate 22 (stageStep G seed time) (stageStep_fixes_clock G seed time))

def finish : Command (Cell G) α 35 := ConcatenationGenerator.finish G G

noncomputable def command (sourceSeed sourceTime seed : PolynomialBound) : Command (Cell G) α 35 :=
  (BoundedSource.prepareCommand .unit Symbol.bit seed).seq
    ((body G sourceSeed sourceTime).command.seq (finish G))

end ComplexityOfGenerators.Simulation.StarGenerator
