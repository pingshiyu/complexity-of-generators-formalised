import ComplexityOfGenerators.Simulation.StarPaths.NativeProposal

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] proposalCoin proposalLoop proposalSetup proposalRoutine

private theorem proposalSetup_fields {O : Type} (s : Store) :
    (proposalSetup (O := O)).eval s 31 = [] ∧
      ((proposalSetup (O := O)).eval s 18).length = (s 22).length-1 ∧
      (proposalSetup (O := O)).eval s 17 = s 17 ∧ (proposalSetup (O := O)).eval s 22 = s 22 := by
  simp [proposalSetup,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.assign_eval,
    WordStack.Routine.ofLocal,Local.eval_pop,List.length_tail]

/-- The actual bounded native proposal reads one cut coin between adjacent
unary units and implements the full-support positive composition proposal. -/
theorem proposalRoutine_value {O : Type} (s : Store) (n : ℕ) (bits : List Bool)
    (size : (s 22).length = n) (coins : s 17 = bits.map coinSymbol) :
    (proposalRoutine (O := O)).eval s 31 = payload (proposal n bits) ∧
      (proposalRoutine (O := O)).eval s 17 = (bits.drop (n-1)).map coinSymbol := by
  let ready := (proposalSetup (O := O)).eval s
  have fields := proposalSetup_fields (O := O) s
  have readyMaster : ready 22 = s 22 := fields.2.2.2
  have readyBuffer : ready 31 = [] := fields.1
  have readySize : (ready 22).length = n := by rw [readyMaster,size]
  have actual : (proposalRoutine (O := O)).eval s = (proposalFinish (O := O)).eval ready := by
    unfold proposalRoutine
    rfl
  rw [actual]
  have readyCoins : ready 17 = bits.map coinSymbol := fields.2.2.1.trans coins
  have readyClock : (ready 18).length = n-1 := by rw [fields.2.1,size]
  by_cases zero : n = 0
  · have empty : ready 22 = [] := List.length_eq_zero_iff.mp (readySize.trans zero)
    unfold proposalFinish
    simp only [WordStack.Routine.branch,empty,List.head?_nil,Option.isSome_none,Bool.false_eq_true,ite_false,
      WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.eval]
    exact ⟨by simpa [proposal,zero,payload] using readyBuffer,by simpa [zero] using readyCoins⟩
  · have nonempty : ready 22 ≠ [] := by intro empty; simp [empty] at readySize; omega
    let started := Function.update ready 31 [Symbol.unit]
    have startedCoins : started 17 = bits.map coinSymbol := by simpa [started] using readyCoins
    have startedBuffer : started 31 = List.replicate 1 .unit++payload [] := by simp [started,payload]
    have loop := proposalLoop_counted (O := O) (n-1) bits 1 [] started startedCoins startedBuffer
    have loopClock : (started 18).length = n-1 := by simpa [started] using readyClock
    have contents : (proposalLoop (O := O)).eval started 17 = (bits.drop (n-1)).map coinSymbol := by
      unfold proposalLoop
      change ((WordStack.Routine.counted 18 (proposalCoin (O := O))).eval^[(started 18).length] started) 17 = _
      rw [loopClock]
      exact loop.1
    have result : Symbol.cut::(proposalLoop (O := O)).eval started 31 = payload (proposal n bits) := by
      unfold proposalLoop
      change Symbol.cut::((WordStack.Routine.counted 18 (proposalCoin (O := O))).eval^[(started 18).length] started) 31 = _
      rw [loopClock]
      simpa only [proposal,if_neg zero] using loop.2
    unfold proposalFinish
    have present : (ready 22).head?.isSome = true := by
      cases word : ready 22 with
      | nil => exact False.elim (nonempty word)
      | cons a rest => rfl
    simp only [WordStack.Routine.branch,present,ite_true,WordStack.Routine.seq,WordStack.Routine.ofLocal,Local.eval_push,readyBuffer,Function.update_self,Function.update_of_ne (by decide : (17 : Fin 35) ≠ 31)]
    change (Symbol.cut::(proposalLoop (O := O)).eval started 31 = _) ∧
      ((proposalLoop (O := O)).eval started 17 = _)
    exact ⟨result,contents⟩

end ComplexityOfGenerators.Simulation.StarPaths
