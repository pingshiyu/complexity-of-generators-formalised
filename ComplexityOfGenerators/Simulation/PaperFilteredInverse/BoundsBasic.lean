import ComplexityOfGenerators.Simulation.PaperFilteredInverse.EvalBasic
import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Prepare

namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

theorem assign_cost_bound (src dst scratch : Fin 35) (sd : src≠dst) (st : src≠scratch) (dt : dst≠scratch)
    (f : Cell M W→Cell M W) (s : Store M W) (cap : ℕ) (sizes : StoreBound s cap) :
    (WordStack.Routine.assign (O:=α) src dst scratch sd st dt f).cost s≤20*cap+3 := by
  rw [WordStack.Routine.assign_cost]
  have hs:=sizes src;have hd:=sizes dst;have ht:=sizes scratch
  omega

theorem flag_bound (reg : Fin 35) (yes : Bool) (s : Store M W) (cap : ℕ)
    (sizes : StoreBound s cap) (positive : 1≤cap) :
    StoreBound ((flag M W reg yes).eval s) cap ∧ (flag M W reg yes).cost s≤3*cap+2 := by
  constructor
  · rw [flag_eval]
    apply sizes.update
    cases yes <;>simp <;>omega
  · have size:=sizes reg
    cases yes <;>simp [flag,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.ofLocal,
      Local.push,Local.ticks,WordStack.Routine.skip,Local.skip] <;>omega

theorem sourceFlag_bound (s : Store M W) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1≤cap) :
    StoreBound ((sourceFlag M W).eval s) cap ∧ (sourceFlag M W).cost s≤3*cap+3 := by
  have yes := flag_bound M W 26 true s cap sizes positive
  have no := flag_bound M W 26 false s cap sizes positive
  constructor
  · dsimp [sourceFlag,WordStack.Routine.branch]
    split <;>first | exact yes.1 | exact no.1
  · dsimp [sourceFlag,WordStack.Routine.branch]
    split <;>omega

theorem sourceFlag_frame (s : Store M W) (j : Fin 35) (different : j≠26) :
    (sourceFlag M W).eval s j=s j := by
  dsimp [sourceFlag,WordStack.Routine.branch]
  split <;>simp [flag_eval,different]

theorem drain_bound (counter first second : Fin 35) (cf : counter≠first) (cs : counter≠second)
    (fs : first≠second) (s : Store M W) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((DrainPair.routine (O:=α) counter first second cf cs).eval s) cap := by
  rw [DrainPair.routine_eval counter first second cf cs fs]
  apply ((sizes.clear counter).update first _ ?_).update second _ ?_
  · exact (by rw [List.length_drop];exact (Nat.sub_le _ _).trans (sizes first))
  · exact (by rw [List.length_drop];exact (Nat.sub_le _ _).trans (sizes second))

theorem atMost_bound (s : Store M W) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1≤cap) :
    StoreBound ((atMost M W).eval s) cap ∧ (atMost M W).cost s≤80*(cap+1) := by
  constructor
  · rw [atMost_eval]
    apply ((((sizes.clear 33).clear 30).update 29 _ ?_).clear 31).update 27 _ ?_
    · exact (by rw [List.length_drop];exact (Nat.sub_le _ _).trans (sizes 25))
    · split_ifs <;>simp <;>omega
  · let a := (WordStack.Routine.assign (O:=α) 13 30 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit)).eval s
    let b := (WordStack.Routine.assign (O:=α) 25 29 33 (by decide) (by decide) (by decide) id).eval a
    let c := Function.update b 31 []
    let d := (DrainPair.routine (O:=α) 30 29 31 (by decide) (by decide)).eval c
    have aBound : StoreBound a cap := sizes.assign (O:=α) 13 30 33 (by decide) (by decide) (by decide) _
    have bBound : StoreBound b cap := aBound.assign (O:=α) 25 29 33 (by decide) (by decide) (by decide) id
    have cBound : StoreBound c cap := bBound.clear 31
    have dBound : StoreBound d cap := drain_bound M W 30 29 31 (by decide) (by decide) (by decide) c cap cBound
    have aCost := assign_cost_bound M W 13 30 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit) s cap sizes
    have bCost := assign_cost_bound M W 25 29 33 (by decide) (by decide) (by decide) id a cap aBound
    have drainCost := DrainPair.routine_cost (O:=α) (30 : Fin 35) 29 31 (by decide) (by decide) c
    have count:=cBound 30
    have cleared:=bBound 31
    have flagCost : (WordStack.Routine.branch 29 (fun head=>flag M W 27 head.isNone)).cost d≤3*cap+3 := by
      have yes:=flag_bound M W 27 true d cap dBound positive
      have no:=flag_bound M W 27 false d cap dBound positive
      dsimp [WordStack.Routine.branch]
      cases (d 29).head? <;>simp only [Option.isNone_none,Option.isNone_some] <;>omega
    change (WordStack.Routine.assign (O:=α) 13 30 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit)).cost s+1+
      ((WordStack.Routine.assign (O:=α) 25 29 33 (by decide) (by decide) (by decide) id).cost a+1+
      (3*(b 31).length+1+((DrainPair.routine (O:=α) 30 29 31 (by decide) (by decide)).cost c+1+
      (WordStack.Routine.branch 29 (fun head=>flag M W 27 head.isNone)).cost d)))≤_
    simp only [WordStack.Routine.assign_cost] at aCost bCost ⊢
    omega

theorem capture_bound (s : Store M W) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1≤cap)
    (empty : s 25=[]) :
    StoreBound ((capture M W).eval s) cap ∧ (capture M W).cost s≤40*(cap+1) := by
  let a := (sourceFlag M W).eval s
  let b := (WordStack.Routine.assign (O:=α) 12 23 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit)).eval a
  obtain ⟨aBound,aCost⟩ := sourceFlag_bound M W s cap sizes positive
  have bBound : StoreBound b cap := aBound.assign (O:=α) 12 23 33 (by decide) (by decide) (by decide) _
  have bEmpty : b 25=[] := by simp [b,WordStack.Routine.assign_eval,a,sourceFlag_frame,empty]
  constructor
  · change StoreBound ((WordStack.Routine.transfer (O:=α) 10 25 (by decide) (inverseOutput M W)).eval b) cap
    simp only [WordStack.Routine.transfer,bEmpty,List.append_nil]
    apply (bBound.clear 10).update 25 _ ?_
    simpa using bBound 10
  · have assignCost := assign_cost_bound M W 12 23 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit) a cap aBound
    have output:=bBound 10
    change (sourceFlag M W).cost s+1+
      ((WordStack.Routine.assign (O:=α) 12 23 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit)).cost a+1+
      6*(b 10).length)≤_
    simp only [WordStack.Routine.assign_cost] at assignCost ⊢
    omega

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
