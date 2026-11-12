import ComplexityOfGenerators.Simulation.StarPaths.OuterBounds

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem counted_outer_bound {O : Type} (flags : List Bool) (target : ℕ) (s : Store)
    (budget count : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget)
    (represented : DPRep flags 0 s) (within : count ≤ target) :
    StoreBound ((WordStack.Routine.counted 0 (outerBody (O := O))).eval^[count] s)
      (budget+count*(target+3)^2) := by
  induction count with
  | zero => simpa using sizes
  | succ count ih =>
    have prior := ih (by omega)
    let current := (WordStack.Routine.counted 0 (outerBody (O := O))).eval^[count] s
    let popped := Function.update current 0 (current 0).tail
    have currentRep : DPRep flags count current := by
      simpa only [Nat.zero_add] using counted_dp (O := O) flags 0 count s represented
    have poppedRep : DPRep flags count popped := by simpa [popped,DPRep] using currentRep
    have poppedBound : StoreBound popped (budget+count*(target+3)^2) :=
      prior.update 0 _ (by simpa only [List.length_tail] using
        (Nat.sub_le (current 0).length 1).trans (prior 0))
    have next := (outerBody_bound (O := O) flags count target popped
      (budget+count*(target+3)^2) (by omega) poppedBound poppedRep (by omega)).1
    rw [Function.iterate_succ_apply']
    convert next using 1 <;> simp [WordStack.Routine.counted,WordStack.Routine.seq,
      WordStack.Routine.ofLocal,Local.eval_pop,current,popped,Nat.add_mul,Nat.add_assoc]

theorem outerLoop_cost {O : Type} (flags : List Bool) (target : ℕ) (s : Store) (budget : ℕ)
    (positive : 1 ≤ budget) (sizes : StoreBound s budget) (represented : DPRep flags 0 s)
    (clock : (s 0).length = target) :
    (WordStack.Routine.iterate 0 (outerBody (O := O)) outerBody_frame).cost s ≤
      target*(1000*(target+3)^3+4)*(budget+target*(target+3)^2+1) := by
  change WordStack.Routine.loopCost _ _ (s 0).length s ≤ _
  rw [clock]
  apply (WordStack.Routine.loopCost_bound _ _ target
    (1000*(target+3)^3*(budget+target*(target+3)^2+1)+2) s ?_).trans
  · calc
      _ ≤ target*((1000*(target+3)^3+4)*(budget+target*(target+3)^2+1)) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  · intro i within
    let current := (WordStack.Routine.counted 0 (outerBody (O := O))).eval^[i] s
    let popped := Function.update current 0 (current 0).tail
    have prior := counted_outer_bound (O := O) flags target s budget i positive sizes represented (by omega)
    have currentRep : DPRep flags i current := by
      simpa only [Nat.zero_add] using counted_dp (O := O) flags 0 i s represented
    have poppedRep : DPRep flags i popped := by simpa [popped,DPRep] using currentRep
    have upper : budget+i*(target+3)^2 ≤ budget+target*(target+3)^2 :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt within)) _
    have poppedBound : StoreBound popped (budget+target*(target+3)^2) :=
      (prior.mono upper).update 0 _ (by simpa only [List.length_tail] using
        (Nat.sub_le (current 0).length 1).trans ((prior 0).trans upper))
    have cost := (outerBody_bound (O := O) flags i target popped
      (budget+target*(target+3)^2) (by omega) poppedBound poppedRep within).2
    change 1+1+(outerBody (O := O)).cost popped ≤ _
    omega

theorem prepare_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepare (O := O)).eval s) (budget+1) ∧
      (prepare (O := O)).cost s ≤ 200*(budget+1) := by
  let cleared := (WordStack.Routine.clearMany (O := O) owned).eval s
  let assigned := (WordStack.Routine.assign (O := O) 22 0 12 (by decide) (by decide) (by decide)
    (fun _ => Symbol.unit)).eval cleared
  have clearedBound : StoreBound cleared budget := sizes.clearMany owned
  have assignedBound : StoreBound assigned budget :=
    clearedBound.assign 22 0 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)
  have four : assigned 4 = [] := by
    simp [assigned,cleared,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval,owned]
  have eleven : assigned 11 = [] := by
    simp [assigned,cleared,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval,owned]
  constructor
  · change StoreBound (Function.update (Function.update assigned 4 (Symbol.present::assigned 4))
      11 (Symbol.present::assigned 11)) _
    exact ((assignedBound.mono (by omega)).update 4 _ (by simp [four])).update 11 _ (by simp [eleven])
  · have clearing := WordStack.Routine.clearMany_cost (O := O) owned s budget (fun j _ => sizes j)
    have count : owned.length ≤ 35 := by
      exact List.length_filter_le _ _ |>.trans (by simp)
    have clearCost : (WordStack.Routine.clearMany (O := O) owned).cost s ≤ 35*(3*budget+1) :=
      clearing.trans (Nat.mul_le_mul_right _ count)
    have copying : (WordStack.Routine.assign (O := O) 22 0 12 (by decide) (by decide) (by decide)
        (fun _ => Symbol.unit)).cost cleared ≤ 20*budget+3 := by
      rw [WordStack.Routine.assign_cost]
      have a := clearedBound 0
      have b := clearedBound 12
      have c := clearedBound 22
      omega
    change (WordStack.Routine.clearMany (O := O) owned).cost s+1+
      ((WordStack.Routine.assign (O := O) 22 0 12 (by decide) (by decide) (by decide)
        (fun _ => Symbol.unit)).cost cleared+1+(1+1+1)) ≤ _
    omega

/-- Whole bounded native DP: the target-independent caller garbage is paid
for explicitly, and both storage and primitive running time are polynomial. -/
theorem dpRoutine_bound {O : Type} (flags : List Bool) (s : Store) (budget target : ℕ)
    (sizes : StoreBound s budget) (source : s 25 = flagsWord flags) (master : (s 22).length = target) :
    StoreBound ((dpRoutine (O := O)).eval s) (budget+1+target*(target+3)^2) ∧
      (dpRoutine (O := O)).cost s ≤ 200*(budget+1)+1+
        target*(1000*(target+3)^3+4)*(budget+1+target*(target+3)^2+1) := by
  let initialized := (prepare (O := O)).eval s
  have initial := prepare_represents (O := O) flags s source
  have size := prepare_bound (O := O) s budget sizes
  have clock : (initialized 0).length = target := initial.2.trans master
  constructor
  · have after := counted_outer_bound (O := O) flags target initialized (budget+1) target
      (by omega) size.1 initial.1 le_rfl
    change StoreBound ((WordStack.Routine.counted 0 (outerBody (O := O))).eval^[(initialized 0).length] initialized) _
    rw [clock]
    exact after
  · have cost := outerLoop_cost (O := O) flags target initialized (budget+1) (by omega) size.1 initial.1 clock
    change (prepare (O := O)).cost s+1+
      (WordStack.Routine.iterate 0 (outerBody (O := O)) outerBody_frame).cost initialized ≤ _
    omega

end ComplexityOfGenerators.Simulation.StarPaths
