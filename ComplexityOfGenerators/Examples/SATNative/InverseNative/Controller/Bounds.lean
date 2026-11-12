import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Execution
import ComplexityOfGenerators.Examples.SATNative.InverseNative.Bounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
attribute [local irreducible] NativeBody.stepConstant
attribute [local irreducible] NativeSubstitution.prepareStream parse InverseNative.bodyTransform transform

private theorem sizeTest_bound (s : Store) (budget : ℕ) (positive : 0 < budget)
    (sizes : StoreBound s budget) : StoreBound (sizeTest.eval s) budget := by
  rw [sizeTest_eval]
  apply StoreBound.update (((sizes.clear 29).clear 28).clear 27) 33
  split_ifs <;> simp <;> omega

private theorem parse_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (parse.eval s) (budget+1) := by
  have source : NativeBody.stackBound budget (s ∘ slots) := fun j => sizes (slots j)
  have parsed := NativeSubstitution.prepareStream_bound (O := Symbol) (s ∘ slots) budget source
  intro j
  by_cases upper : 32 ≤ j.val
  · rw [parse_upper s j upper]
    exact (sizes j).trans (by omega)
  · let i : Fin 32 := ⟨j.val, by omega⟩
    have same : slots i = j := Fin.ext rfl
    rw [← same, parse_here]
    exact parsed i

private theorem parse_cost (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    parse.cost s ≤ 120*(budget+2) := by
  have source : NativeBody.stackBound budget (s ∘ slots) := fun j => sizes (slots j)
  simpa only [parse,Routine.rename_cost] using NativeSubstitution.prepareStream_cost (O := Symbol) (s ∘ slots) budget source

private theorem moreRoutine_cost (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    moreRoutine.cost s ≤ 100*(budget+1) := by
  let first := (Routine.assign (O := Symbol) 4 27 9 (by decide) (by decide) (by decide) id).eval s
  let second := (Routine.assign (O := Symbol) 10 28 9 (by decide) (by decide) (by decide) id).eval first
  let third := (Routine.clear (S := Symbol) (O := Symbol) 29).eval second
  have drain := DrainPair.routine_cost (O := Symbol) (28 : Fin 35) 27 29 (by decide) (by decide) third
  have count : (third 28).length = (s 10).length := by
    simp [third,second,first,Routine.clear,Routine.assign_eval]
  rw [count] at drain
  have a := sizes 4
  have b := sizes 10
  have c := sizes 27
  have d := sizes 28
  have e := sizes 9
  have f := sizes 29
  change (Routine.assign (O := Symbol) 4 27 9 _ _ _ id).cost s+1+
    ((Routine.assign (O := Symbol) 10 28 9 _ _ _ id).cost first+1+
      (3*(second 29).length+1+(DrainPair.routine (O := Symbol) 28 27 29 _ _).cost third)) ≤ _
  simp [Routine.assign_cost,first,second,Routine.assign_eval] at *
  omega

private theorem masked_bound (n : ℕ) (bits : BitString) (m : Memory)
    (sizes : StoreBound m.store (n+1)) : StoreBound (masked n bits m).store (n+1) := by
  change StoreBound (Function.update (Function.update (Function.update m.store 30 []) 33 []) 31 _) (n+1)
  apply StoreBound.update ((sizes.clear 30).clear 33) 31
  simp only [List.length_map,List.length_take]
  omega

private theorem cleared_bound (n : ℕ) (m : Memory) (sizes : StoreBound m.store (n+1)) :
    StoreBound (m.set 3 []).store (n+1) := by
  exact sizes.clear 3

private theorem finishBitBudget_bound (bit : Bool) (n : ℕ) (bits : BitString) (m : Memory)
    (capacity active : ℕ) (state : NativeBody.State) (represented : Represents capacity active state m.store)
    (sizes : StoreBound m.store (n+1)) (cap : capacity ≤ n) (more : active+1 ≤ capacity)
    (clock : (m.store 16).length ≤ n) :
    finishBitBudget bit n bits m ≤ NativeSubstitution.bodyBudget n+100*(n+2)^2 := by
  let ready := (masked n bits m).store
  have readyRep := masked_represents capacity active state m n bits represented
  have readySizes := masked_bound n bits m sizes
  have sameClock : ready 16 = m.store 16 := (masked_fields n bits m).2 16 (by decide) (by decide) (by decide)
  have readyClock : (ready 16).length ≤ n := by rw [sameClock]; exact clock
  have source : NativeBody.stackBound (n+1) (ready ∘ slots) := fun j => readySizes (slots j)
  have resources := InverseNative.bodyTransform_resources (O := Symbol) bit capacity active state
    (ready ∘ slots) readyRep n source cap more readyClock
  have cost : (transform bit).cost ready ≤ NativeSubstitution.bodyBudget n := by
    simpa only [transform,Routine.rename_cost] using resources.2
  have output21 : ((transform bit).eval ready 21).length ≤ (n+2)^2 := by
    rw [show (21 : Fin 35) = slots 21 from rfl,transform_here]
    exact resources.1 21
  have output28 : ((transform bit).eval ready 28).length ≤ (n+2)^2 := by
    rw [show (28 : Fin 35) = slots 28 from rfl,transform_here]
    exact resources.1 28
  have a := sizes 31
  have b := sizes 33
  have c := sizes 30
  unfold finishBitBudget maskBudget
  dsimp only
  change 3*(m.store 31).length+3*(m.store 33).length+3*(m.store 30).length+26*n+8+
    (transform bit).cost ready+3*((transform bit).eval ready 28).length+
    10*((transform bit).eval ready 21).length+8 ≤ _
  nlinarith

private theorem moreBitBudget_bound (bit : Bool) (n : ℕ) (bits : BitString) (m : Memory)
    (capacity active : ℕ) (state : NativeBody.State) (represented : Represents capacity active state m.store)
    (sizes : StoreBound m.store (n+1)) (cap : capacity ≤ n)
    (clock : (m.store 16).length ≤ n) (bitsSize : bits.length ≤ n+1) :
    moreBitBudget bit n bits m ≤ NativeSubstitution.bodyBudget n+300*(n+2)^2 := by
  have first := moreRoutine_cost m.store (n+1) sizes
  have firstSizes := moreRoutine_preserves m.store (n+1) sizes
  have firstRep := moreRoutine_represents capacity active state m.store represented
  have sameClock : (morePrepared m).store 16 = m.store 16 := moreRoutine_frame m.store 16
    (by decide) (by decide) (by decide) (by decide)
  have firstClock : ((morePrepared m).store 16).length ≤ n := by rw [sameClock]; exact clock
  have capReg : (m.store 4).length = capacity := by
    change ((m.store ∘ slots) 4).length = capacity
    rw [represented.2.1]
    simp only [List.length_replicate]
  have activeReg : (m.store 10).length = active := by
    change ((m.store ∘ slots) 10).length = active
    rw [represented.2.2.1]
    simp only [List.length_replicate]
  unfold moreBitBudget
  by_cases more : active+1 ≤ capacity
  · rw [if_pos (by simpa only [capReg,activeReg] using more)]
    have last := finishBitBudget_bound bit n bits (morePrepared m) capacity active state firstRep firstSizes cap more firstClock
    nlinarith
  · rw [if_neg (by simpa only [capReg,activeReg] using more)]
    nlinarith

private theorem labelBudget_bound (n : ℕ) (bits : BitString) (m : Memory)
    (capacity active : ℕ) (state : NativeBody.State) (represented : Represents capacity active state m.store)
    (sizes : StoreBound m.store (n+1)) (cap : capacity ≤ n)
    (clock : (m.store 16).length ≤ n) (bitsSize : bits.length ≤ n+1) :
    labelBudget n bits m ≤ 2*NativeSubstitution.bodyBudget n+1000*(n+2)^2 := by
  have rep := clearedLabel_represents capacity active state m represented
  have clearSizes := cleared_bound n m sizes
  have clearClock : ((m.set 3 []).store 16).length ≤ n := by simpa using clock
  have no := moreBitBudget_bound false n bits (m.set 3 []) capacity active state rep clearSizes cap clearClock bitsSize
  have yes := moreBitBudget_bound true n bits (m.set 3 []) capacity active state rep clearSizes cap clearClock bitsSize
  have saved := sizes 34
  unfold labelBudget
  nlinarith

noncomputable def primitiveTime : PolynomialBound := PolynomialBound.ofPolynomial
  (2*(200*(Polynomial.X+2)+1+
    Polynomial.X*(Polynomial.C (NativeBody.stepConstant+304)*((Polynomial.X+2)^2+1)))+
    2000*(Polynomial.X+2)^2)

theorem primitiveTime_seed (n : ℕ) : n+1 ≤ primitiveTime n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

attribute [local irreducible] inputRoutine sizeTest loaded preparedStore prepared indexed sized parsed
  labelBudget NativeSubstitution.bodyBudget

theorem commandBudget_bound {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (label : List Symbol) (bits : BitString)
    (targetSize : (formula.encode capacity active).length ≤ n) (labelSize : label.length ≤ n)
    (bitsSize : bits.length ≤ n+1) :
    commandBudget n (formula.encode capacity active) label bits ≤ primitiveTime n := by
  let target := formula.encode capacity active
  have positive : 0 < n := by
    have length := formula.encode_length bound valid
    omega
  have cap : capacity ≤ n := by
    have length := formula.encode_length bound valid
    omega
  have readySizes := prepared_bound n target label targetSize labelSize
  have sizedStore : (sized n target label).store = sizeTest.eval (preparedStore n target label) := by unfold sized; rfl
  have parsedStore : (parsed n target label).store = parse.eval (sized n target label).store := by unfold parsed; rfl
  have sizedSizes : StoreBound (sized n target label).store n := by
    rw [sizedStore]
    exact sizeTest_bound _ n positive readySizes
  have parsedSizes : StoreBound (parsed n target label).store (n+1) := by
    rw [parsedStore]
    exact parse_bound _ n sizedSizes
  have word : (sized n target label).store 2 = target := by
    rw [sizedStore,
      sizeTest_frame _ _ (by decide) (by decide) (by decide) (by decide)]
    simp [preparedStore]
  have properties := parse_canonical bound formula (sized n target label).store word
  have parsedRep : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ (parsed n target label).store := by
    rw [parsedStore]
    exact properties.1
  have clock : ((parsed n target label).store 16).length ≤ n := by
    rw [parsedStore,properties.2]
    have body : (formula.bodyWord capacity).length ≤ target.length := by
      simp only [target,Formula.encode,Formula.bodyWord,List.length_append,List.length_replicate,List.length_singleton]
      omega
    exact body.trans targetSize
  have labelCost := labelBudget_bound n bits (parsed n target label) capacity active _ parsedRep parsedSizes cap clock bitsSize
  have inputCost := inputRoutine_cost n target label
  have sizeCost : sizeTest.cost (preparedStore n target label) ≤ 80*(n+1) :=
    by simpa only [sizeTest] using LengthTest.routine_cost (O := Symbol) sizeSlots Symbol.one _ n readySizes
  have parseCost := parse_cost (sized n target label).store n sizedSizes
  have result : commandBudget n target label bits ≤ 2*NativeSubstitution.bodyBudget n+2000*(n+2)^2 := by
    unfold commandBudget
    rw [show (indexed n target label).store = (Command.loadedIndex 32 .zero n (loaded target label)).store from by unfold indexed; rfl,
      inputCost]
    nlinarith
  apply result.trans
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  unfold NativeSubstitution.bodyBudget
  rfl

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
