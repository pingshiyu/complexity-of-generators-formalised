import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.PrefixBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Correctness
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelBitsBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelChecksBounds
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
open Simulation.WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] capacity singleton labelPrepare label LabelBits.routine LabelChecks.routine

theorem capacity_bound (s : Store) (budget n : ℕ) (sizes : StoreBound s budget)
    (base : (s 37).length+1 ≤ budget) (room : BaseSearch.square (s 37).length+1 ≤ budget)
    (parentBound : (s 37).length ≤ n+2) :
    StoreBound (capacity.eval s) budget ∧
      capacity.cost s ≤ 120*(budget+1)+Command.counterBudget BaseSearch.square (n+2) := by
  let counted := (CounterRoutine.routine (O := Symbol) counterSlots BaseSearch.square (.bit true)).eval s
  let pushed := Function.update counted 46 (.bit true::counted 46)
  let compared := (RationalSelection.Compare.routine (O := Symbol) capacitySlots (.bit true)).eval pushed
  have countedSize : StoreBound counted budget := sizes.counter counterSlots BaseSearch.square (.bit true)
    (by simpa [counterSlots] using base) (by simpa [counterSlots] using (by omega : BaseSearch.square (s 37).length ≤ budget))
  have countedCost : (CounterRoutine.routine (O := Symbol) counterSlots BaseSearch.square (.bit true)).cost s ≤
      26*budget+7+Command.counterBudget BaseSearch.square (s 37).length := by
    simpa only [show counterSlots 0 = (37 : Fin 64) from rfl] using
      CounterRoutine.routine_cost (O := Symbol) counterSlots BaseSearch.square (.bit true) s budget sizes
  have length : (counted 46).length = BaseSearch.square (s 37).length := by
    simp [counted,CounterRoutine.routine_eval,counterSlots]
  have pushedSize : StoreBound pushed budget := countedSize.update 46 _ (by simpa [length] using room)
  have comparedSize : StoreBound compared budget := pushedSize.strictCompare capacitySlots (.bit true) (by omega)
  have comparedCost := RationalSelection.Compare.routine_cost (O := Symbol) capacitySlots (.bit true) pushed budget pushedSize
  have checked := require_bound 20 false compared budget comparedSize
  constructor
  · unfold capacity
    exact checked.1
  · have monotone := (Command.counterBudget BaseSearch.square).monotone parentBound
    unfold capacity
    change (CounterRoutine.routine (O := Symbol) counterSlots BaseSearch.square (.bit true)).cost s+1+
      (1+1+((RationalSelection.Compare.routine (O := Symbol) capacitySlots (.bit true)).cost pushed+1+
        (require 20 false).cost compared)) ≤ _
    have checkedCost := checked.2
    omega

theorem singleton_bound (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound (singleton.eval s) budget ∧ singleton.cost s ≤ 100*(budget+1) := by
  let cleared := Function.update s 49 []
  let pushed := Function.update cleared 49 [Symbol.bit true]
  let tested := (LengthTest.routine (O := Symbol) singletonSlots (.bit true)).eval pushed
  have pushedSize : StoreBound pushed budget := (sizes.clear 49).update 49 _ (by simpa using positive)
  have testedSize : StoreBound tested budget := pushedSize.lengthTest singletonSlots (.bit true) positive
  have testCost := LengthTest.routine_cost (O := Symbol) singletonSlots (.bit true) pushed budget pushedSize
  have checked := require_bound 20 true tested budget testedSize
  constructor
  · unfold singleton
    exact checked.1
  · have old := sizes 49
    have final := checked.2
    unfold singleton
    change 3*(s 49).length+1+(1+1+((LengthTest.routine (O := Symbol) singletonSlots (.bit true)).cost pushed+1+
      (require 20 true).cost tested)) ≤ _
    omega

theorem labelPrepare_bound (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound (labelPrepare.eval s) budget ∧ labelPrepare.cost s ≤ 100*(budget+1) := by
  let a := (Routine.assign (O := Symbol) 33 25 48 (by decide) (by decide) (by decide) id).eval s
  let b := (Routine.assign (O := Symbol) 38 19 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval a
  let c := (Routine.assign (O := Symbol) 37 27 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval b
  let d := (Routine.assign (O := Symbol) 37 26 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval c
  have aSize : StoreBound a budget := sizes.assign _ _ _ _ _ _ _
  have bSize : StoreBound b budget := aSize.assign _ _ _ _ _ _ _
  have cSize : StoreBound c budget := bSize.assign _ _ _ _ _ _ _
  have dSize : StoreBound d budget := cSize.assign _ _ _ _ _ _ _
  have aCost := assign_cost 33 25 48 (by decide) (by decide) (by decide) id s budget sizes
  have bCost := assign_cost 38 19 48 (by decide) (by decide) (by decide) (fun _ => .bit true) a budget aSize
  have cCost := assign_cost 37 27 48 (by decide) (by decide) (by decide) (fun _ => .bit true) b budget bSize
  have dCost := assign_cost 37 26 48 (by decide) (by decide) (by decide) (fun _ => .bit true) c budget cSize
  constructor
  · rw [labelPrepare_eval]
    unfold labelStore
    exact (((((sizes.update 25 (s 33) (sizes 33)).update 19 _ (by simpa using sizes 38)).update
      27 _ (by simpa using sizes 37)).update 26 _ (by simpa using sizes 37)).update
        16 [Symbol.bit true] (by simpa using positive)).clear 48
  · have old := dSize 16
    unfold labelPrepare
    change (Routine.assign (O := Symbol) 33 25 48 _ _ _ id).cost s+1+
      ((Routine.assign (O := Symbol) 38 19 48 _ _ _ (fun _ => .bit true)).cost a+1+
        ((Routine.assign (O := Symbol) 37 27 48 _ _ _ (fun _ => .bit true)).cost b+1+
          ((Routine.assign (O := Symbol) 37 26 48 _ _ _ (fun _ => .bit true)).cost c+1+(3*(d 16).length+1+1)))) ≤ _
    omega

theorem label_bound (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget)
    (range : 2^(s 38).length ≤ budget) :
    StoreBound (label.eval s) (10*(budget+1)) ∧ label.cost s ≤ 3000*(10*(budget+1)+1)^2 := by
  let prepared := labelPrepare.eval s
  let decoded := ((LabelBits.routine (O := Symbol)).rename Output.low32).eval prepared
  let checked := ((LabelChecks.routine (O := Symbol)).rename Output.low32).eval decoded
  let copied := (Routine.assign (O := Symbol) 28 39 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval checked
  have preparedBound := labelPrepare_bound s budget positive sizes
  have lowSize : StoreBound (prepared ∘ Output.low32) budget := fun j => preparedBound.1 _
  have width : ((prepared ∘ Output.low32) 19).length = (s 38).length := by
    change (prepared 19).length = (s 38).length
    simp [prepared,labelPrepare_eval,labelStore]
  have nativeDecoded := LabelBits.routine_bound (O := Symbol) (prepared ∘ Output.low32) budget lowSize (by rw [width]; exact range)
  have decodedSize : StoreBound decoded (10*(budget+1)) := call32_bound _ prepared budget _ preparedBound.1 (by omega) nativeDecoded.1
  have decodedCost : ((LabelBits.routine (O := Symbol)).rename Output.low32).cost prepared ≤ 2000*(budget+1)^2 := by
    simpa only [Routine.rename_cost] using nativeDecoded.2
  have checkedLowSize : StoreBound (decoded ∘ Output.low32) (10*(budget+1)) := fun j => decodedSize _
  have nativeChecked := LabelChecks.routine_bound (O := Symbol) (decoded ∘ Output.low32) (10*(budget+1)) (by omega) checkedLowSize
  have checkedSize : StoreBound checked (10*(budget+1)) := call32_bound _ decoded _ _ decodedSize le_rfl nativeChecked.1
  have checkedCost : ((LabelChecks.routine (O := Symbol)).rename Output.low32).cost decoded ≤ 320*(10*(budget+1)+1) := by
    simpa only [Routine.rename_cost] using nativeChecked.2
  have copiedSize : StoreBound copied (10*(budget+1)) := checkedSize.assign _ _ _ _ _ _ _
  have copiedCost := assign_cost 28 39 48 (by decide) (by decide) (by decide) (fun _ => .bit true) checked (10*(budget+1)) checkedSize
  have final := require_bound 16 true copied (10*(budget+1)) copiedSize
  constructor
  · unfold label
    exact final.1
  · unfold label
    change labelPrepare.cost s+1+(((LabelBits.routine (O := Symbol)).rename Output.low32).cost prepared+1+
      (((LabelChecks.routine (O := Symbol)).rename Output.low32).cost decoded+1+
        ((Routine.assign (O := Symbol) 28 39 48 _ _ _ (fun _ => .bit true)).cost checked+1+(require 16 true).cost copied))) ≤ _
    have preparedCost := preparedBound.2
    have finalCost := final.2
    nlinarith

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
