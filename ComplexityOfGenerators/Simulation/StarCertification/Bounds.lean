import ComplexityOfGenerators.Simulation.StarCertification.Iteration
import ComplexityOfGenerators.Simulation.StarCertification.PrimitiveBounds

namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] body bodyPrefix trial record prepare scan finish routine stepBudget

/-- Both store and primitive runtime bounds follow the actual counted
source-test controller, without an assumed machine or variance bound. -/
theorem counted_bound (p : PolynomialBound) (start count n cap : ℕ) (prior : List Bool) (bits : BitString) (s : Store M)
    (stored : Stored M start prior bits s) (priorBound : prior.length ≤ start) (indexBound : start+count ≤ n)
    (sizes : StoreBound s cap) (base : n+1 ≤ cap)
    (seedBound : IndexwiseCertification.seed p n ≤ cap) (timeBound : IndexwiseCertification.clock p n+1 ≤ cap)
    (space : 1+n+IndexwiseCertification.seed p n+3*(IndexwiseCertification.clock p n+1) ≤ cap) :
    StoreBound ((WordStack.Routine.counted 23 (body M p)).eval^[count] s) cap ∧
      WordStack.Routine.loopCost (WordStack.Routine.counted 23 (body M p)).cost
        (WordStack.Routine.counted 23 (body M p)).eval count s ≤ count*(stepBudget M p n cap+4) := by
  induction count generalizing start prior bits s with
  | zero => exact ⟨sizes,by simp [WordStack.Routine.loopCost]⟩
  | succ count ih =>
      let popped := Function.update s 23 (s 23).tail
      let ready := (WordStack.Routine.counted 23 (body M p)).eval s
      have poppedSize : StoreBound popped cap := sizes.update 23 _ (by have := sizes 23; simp only [List.length_tail]; omega)
      have poppedStored : Stored M start prior bits popped := by
        constructor
        · simpa [popped] using stored.counter
        · simpa [popped] using stored.random
        · simpa [popped] using stored.cache
      have first := body_bound M p start n cap prior bits popped poppedStored priorBound (by omega)
        poppedSize base seedBound timeBound space
      have nextStored : Stored M (start+1) (testFlag M p (start+1) bits::prior)
          (bits.drop (IndexwiseCertification.seed p (start+1))) ready := body_stored M p start prior bits popped poppedStored
      have nextSize : StoreBound ready cap := first.1
      have next := ih (start+1) (testFlag M p (start+1) bits::prior)
        (bits.drop (IndexwiseCertification.seed p (start+1))) ready nextStored (by simp; omega) (by omega) nextSize
      constructor
      · rw [Function.iterate_succ_apply]
        exact next.1
      · rw [WordStack.Routine.loopCost]
        have current : (WordStack.Routine.counted 23 (body M p)).cost s ≤ stepBudget M p n cap+2 := by
          change 1+1+(body M p).cost popped ≤ _
          omega
        have tail := next.2
        change (WordStack.Routine.counted 23 (body M p)).cost s+2+
          WordStack.Routine.loopCost _ _ count ready ≤ _
        nlinarith

theorem prepare_bound (s : Store M) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((prepare M).eval s) cap ∧ (prepare M).cost s ≤ 30*(cap+1) := by
  constructor
  · unfold prepare
    exact ((sizes.clear 24).clear 25).assign (O := α) 22 23 33 (by decide) (by decide) (by decide) (fun _ => unit M)
  · have a := sizes 24
    have b := sizes 25
    have c := sizes 23
    have d := sizes 33
    have e := sizes 22
    simp [prepare,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.assign_cost]
    omega

theorem finish_eval (s : Store M) :
    (finish M).eval s = Function.update (Function.update (Function.update s 25 (s 25).reverse) 33 []) 34 [] := by
  funext j
  by_cases a : j = 25 <;> by_cases b : j = 33 <;> by_cases c : j = 34 <;>
    simp [finish,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.transfer,
      WordStack.Routine.assign_eval,a,b,c]

theorem finish_bound (s : Store M) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((finish M).eval s) cap ∧ (finish M).cost s ≤ 30*(cap+1) := by
  constructor
  · rw [finish_eval]
    exact ((sizes.update 25 _ (by simpa using sizes 25)).clear 33).clear 34
  · have a := sizes 34
    have b := sizes 25
    have c := sizes 33
    simp [finish,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.transfer,
      WordStack.Routine.assign_cost]
    omega

noncomputable def routineBudget (p : PolynomialBound) (n cap : ℕ) : ℕ := n*(stepBudget M p n cap+4)+100*(cap+1)

theorem routine_bound (p : PolynomialBound) (s : Store M) (bits : BitString) (n cap : ℕ)
    (coins : s 17 = bits.map (bitSymbol M)) (size : (s 22).length = n)
    (sizes : StoreBound s cap) (base : n+1 ≤ cap)
    (seedBound : IndexwiseCertification.seed p n ≤ cap) (timeBound : IndexwiseCertification.clock p n+1 ≤ cap)
    (space : 1+n+IndexwiseCertification.seed p n+3*(IndexwiseCertification.clock p n+1) ≤ cap) :
    StoreBound ((routine M p).eval s) cap ∧ (routine M p).cost s ≤ routineBudget M p n cap := by
  let prepared := (prepare M).eval s
  let tested := (scan M p).eval prepared
  have initialized := prepare_fields M s bits coins
  obtain ⟨preparedSize,preparedCost⟩ := prepare_bound M s cap sizes
  have scanResult := counted_bound M p 0 n n cap [] bits prepared initialized.1 (by simp) (by simp)
    preparedSize base seedBound timeBound space
  have clock : (prepared 23).length = n := initialized.2.trans size
  have testedSize : StoreBound tested cap := by
    unfold tested scan
    change StoreBound (((WordStack.Routine.counted 23 (body M p)).eval^[(prepared 23).length]) prepared) cap
    rw [clock]
    exact scanResult.1
  have scanCost : (scan M p).cost prepared ≤ n*(stepBudget M p n cap+4) := by
    unfold scan
    change WordStack.Routine.loopCost _ _ (prepared 23).length prepared ≤ _
    rw [clock]
    exact scanResult.2
  obtain ⟨finalSize,finalCost⟩ := finish_bound M tested cap testedSize
  constructor
  · unfold routine
    exact finalSize
  · unfold routine
    change (prepare M).cost s+1+((scan M p).cost prepared+1+(finish M).cost tested) ≤ _
    unfold routineBudget
    omega

end ComplexityOfGenerators.Simulation.StarCertification
