import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Native
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.SamplingBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Bounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Bounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000

noncomputable def primitiveBudget (n : ℕ) : ℕ :=
  let base := Classify.storeBudget n
  let chosen := Choose.storeBudget base
  Classify.time n+100*(base+1)+100*(n+1)+10*seed n+
    Choose.stackBudget base+Output.stackBudget chosen+4*Output.storeBudget chosen+100

theorem commandBudget_bound (graph : Graph) (start n : ℕ) (label : List Symbol) (bits : BitString)
    (inside : start<graph.size) (targetSize : (graph.encode start).length≤n)
    (labelSize : label.length≤n) (bitsSize : bits.length≤seed n) :
    commandBudget n (graph.encode start) label bits≤primitiveBudget n := by
  let target := graph.encode start
  let source := classified n target label
  let base := Classify.storeBudget n
  let output := Choose.storeBudget base
  have initial := prepared_bound n target label targetSize labelSize
  have index : (preparedStore n target label 34).length=n := by simp [preparedStore]
  have classifier := Classify.routine_bound (preparedStore n target label) n initial index
  have sourceBound : StoreBound source.store base := classifier.1
  have sourceTime : Classify.routine.cost (preparedStore n target label)≤Classify.time n :=
    classifier.2.trans (Classify.stackBudget_le n)
  have views := classified_graph graph start n label inside
  have sizeBound : graph.size≤n := by
    rw [Graph.encode_length] at targetSize
    unfold encodingLength at targetSize
    omega
  have positive : 0<graph.size+1 := by omega
  have widthBound := width_le_size (graph.size+1)
  have room : (source.store 38).length+2*(source.store 35).length≤base := by
    rw [views.labelWidth,views.childSize]
    simp only [List.length_replicate]
    unfold base Classify.storeBudget
    nlinarith
  have sampledBound : StoreBound (sampled bits source).store base := sampled_bound bits source base sourceBound room
  have range : 2^((sampled bits source).store 38).length≤base := by
    rw [sampled_width,views.labelWidth,List.length_replicate]
    have power := RationalSelection.pow_clog_le_twice (graph.size+1) positive
    change 2^(Nat.clog 2 (graph.size+1))≤base
    unfold base Classify.storeBudget
    nlinarith
  have choosing := Choose.routine_bound (sampled bits source).store base sampledBound range
  have chosenBound : StoreBound (chosen bits source).store output := choosing.1
  have finishCost := finishBudget_bound (chosen bits source).store output chosenBound
  have clockCost := sampleClock_cost source.store base sourceBound
  have source42 := sourceBound 42
  have source47 := sourceBound 47
  have clockBound : ((counted source).store 46).length≤base := (counted_bound source base sourceBound room) 46
  have randomCost : randomBudget bits source≤80*(base+1)+Choose.stackBudget base+
      Output.stackBudget output+4*Output.storeBudget output+seed n+30 := by
    have chooseCost := choosing.2
    unfold randomBudget
    change Choose.routine.cost (sampled bits source).store≤Choose.stackBudget base at chooseCost
    omega
  have inputBound : input.cost (indexed n target label).store≤12*n+4 := by
    rw [input_cost]
    change target.length≤n at targetSize
    omega
  have savedLength : (source.store 32).length≤n := by rw [views.raw]; exact targetSize
  have dispatchCost : dispatchBudget bits source≤4*n+
      (80*(base+1)+Choose.stackBudget base+Output.stackBudget output+4*Output.storeBudget output+seed n+30)+seed n+3 := by
    unfold dispatchBudget
    omega
  change commandBudget n target label bits≤Classify.time n+100*(base+1)+100*(n+1)+10*seed n+
    Choose.stackBudget base+Output.stackBudget output+4*Output.storeBudget output+100
  unfold commandBudget
  change dispatchBudget bits (classified n target label)≤_ at dispatchCost
  omega

private noncomputable def basePolynomial : Polynomial ℕ := 1000*(Polynomial.X+2)^2
private noncomputable def chosenPolynomial : Polynomial ℕ := 10*(basePolynomial+1)+4
private noncomputable def primitivePolynomial : Polynomial ℕ :=
  Classify.time.asPolynomial+100*(basePolynomial+1)+100*(Polynomial.X+1)+30*(Polynomial.X+1)+
    100000*(basePolynomial+4)^2+
    (100000*(chosenPolynomial+5)^4+10000*(chosenPolynomial+5)^2+10000*(chosenPolynomial+5))+
    4*(40*(chosenPolynomial+5)^2+6)+100

noncomputable def primitiveTime : PolynomialBound := PolynomialBound.ofPolynomial primitivePolynomial

theorem primitiveBudget_le (n : ℕ) : primitiveBudget n≤primitiveTime n := by
  have bounded := PolynomialBound.eval_le_ofPolynomial primitivePolynomial n
  change _≤primitiveTime n at bounded
  convert bounded using 1
  simp [primitivePolynomial,basePolynomial,chosenPolynomial,primitiveBudget,
    Classify.storeBudget,Choose.storeBudget,Choose.stackBudget,Output.storeBudget,Output.stackBudget,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one,
    PolynomialBound.asPolynomial_eval]
  ring

theorem primitiveTime_seed (n : ℕ) : seed n≤primitiveTime n := by
  apply (show seed n≤primitiveBudget n by dsimp only [primitiveBudget]; omega).trans
  exact primitiveBudget_le n

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
