import ComplexityOfGenerators.Simulation.StarPaths.ProposalComplete
import ComplexityOfGenerators.Simulation.WordStack.GrowingRoutine

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem proposalCoin_cost {O : Type} (s : Store) : (proposalCoin (O := O)).cost s ≤ 10 := by
  simp [proposalCoin,WordStack.Routine.seq,WordStack.Routine.branch,WordStack.Routine.ofLocal,
    Local.push,Local.pop,Local.ticks,WordStack.Routine.skip]
  split_ifs <;> simp <;> omega

theorem proposalCoin_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((proposalCoin (O := O)).eval s) (budget+2) ∧
      (proposalCoin (O := O)).cost s ≤ 10 := by
  constructor
  · by_cases cut : (s 17).head? = some Symbol.bitTrue
    · have target : (proposalCoin (O := O)).eval s = Function.update (Function.update s 31
          (Symbol.unit::Symbol.cut::s 31)) 17 (s 17).tail := by
        simp [proposalCoin,WordStack.Routine.seq,WordStack.Routine.branch,cut,
          WordStack.Routine.ofLocal,Local.eval_push,Local.eval_pop]
      rw [target]
      exact ((sizes.mono (by omega)).update 31 _ (by simpa using Nat.add_le_add_right (sizes 31) 2)).update
        17 _ (by simpa only [List.length_tail] using (Nat.sub_le (s 17).length 1).trans ((sizes 17).trans (by omega)))
    · have target : (proposalCoin (O := O)).eval s = Function.update (Function.update s 31
          (Symbol.unit::s 31)) 17 (s 17).tail := by
        simp [proposalCoin,WordStack.Routine.seq,WordStack.Routine.branch,cut,
          WordStack.Routine.ofLocal,Local.eval_push,Local.eval_pop,WordStack.Routine.skip]
      rw [target]
      exact ((sizes.mono (by omega)).update 31 _ (by simp only [List.length_cons]; have := sizes 31; omega)).update
        17 _ (by simpa only [List.length_tail] using (Nat.sub_le (s 17).length 1).trans ((sizes 17).trans (by omega)))
  · exact proposalCoin_cost s

theorem proposalLoop_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((proposalLoop (O := O)).eval s) (budget+2*(s 18).length) ∧
      (proposalLoop (O := O)).cost s ≤ 14*(s 18).length := by
  constructor
  · have bound := WordStack.Routine.iterate_growing_bound 18 (proposalCoin (O := O)) (fun _ => True)
      0 2 (by intros; trivial) (by intros; trivial)
      (fun t b _ _ h => (proposalCoin_bound (O := O) t b h).1)
      (proposalCoin_frame 18 (by decide) (by decide)) s budget (by omega) trivial sizes
    simpa only [proposalLoop,Nat.mul_comm] using bound.2
  · change WordStack.Routine.loopCost _ _ (s 18).length s ≤ _
    apply (WordStack.Routine.loopCost_bound _ _ (s 18).length 12 s ?_).trans (by omega)
    intro i within
    let current := (WordStack.Routine.counted 18 (proposalCoin (O := O))).eval^[i] s
    let popped := Function.update current 18 (current 18).tail
    have cost := proposalCoin_cost (O := O) popped
    change 1+1+(proposalCoin (O := O)).cost popped ≤ _
    omega

theorem proposalSetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((proposalSetup (O := O)).eval s) budget ∧
      (proposalSetup (O := O)).cost s ≤ 30*(budget+1) := by
  let cleared := Function.update s 31 []
  let copied := (WordStack.Routine.assign (O := O) 22 18 12 (by decide) (by decide) (by decide)
    (fun _ => Symbol.unit)).eval cleared
  have copiedBound : StoreBound copied budget :=
    (sizes.clear 31).assign 22 18 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)
  constructor
  · change StoreBound (Function.update copied 18 (copied 18).tail) budget
    exact copiedBound.update 18 _ (by
      simpa only [List.length_tail] using (Nat.sub_le (copied 18).length 1).trans (copiedBound 18))
  · have a := sizes 31
    have b := sizes 18
    have c := sizes 12
    have d := sizes 22
    simp [proposalSetup,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.assign_cost,
      WordStack.Routine.assign_eval,WordStack.Routine.ofLocal,Local.pop,Local.ticks]
    omega

theorem proposalFinish_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((proposalFinish (O := O)).eval s) (3*budget+2) ∧
      (proposalFinish (O := O)).cost s ≤ 20*(budget+1) := by
  by_cases nonzero : (s 22).head?.isSome = true
  · let pushed := Function.update s 31 (Symbol.unit::s 31)
    let walked := (proposalLoop (O := O)).eval pushed
    have pushedBound : StoreBound pushed (budget+1) :=
      (sizes.mono (by omega)).update 31 _ (by simpa using Nat.add_le_add_right (sizes 31) 1)
    have loop := proposalLoop_bound (O := O) pushed (budget+1) pushedBound
    have count : (pushed 18).length = (s 18).length := by simp [pushed]
    have upper : budget+1+2*(pushed 18).length ≤ 3*budget+1 := by rw [count]; have := sizes 18; omega
    simp only [proposalFinish,WordStack.Routine.branch,nonzero,ite_true]
    constructor
    · change StoreBound (Function.update walked 31 (Symbol.cut::walked 31)) _
      exact (loop.1.mono (by omega)).update 31 _ (by
        simp only [List.length_cons]
        have := (loop.1 31).trans upper
        change (walked 31).length ≤ _ at this
        omega)
    · change 1+(1+1+((proposalLoop (O := O)).cost pushed+1+1)) ≤ _
      have cost : (proposalLoop (O := O)).cost pushed ≤ 14*(s 18).length := by simpa only [count] using loop.2
      have := sizes 18
      omega
  · simp only [proposalFinish,WordStack.Routine.branch,nonzero,Bool.false_eq_true,ite_false]
    exact ⟨sizes.mono (by omega),by simp [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.ticks]; omega⟩

theorem proposalRoutine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((proposalRoutine (O := O)).eval s) (3*budget+2) ∧
      (proposalRoutine (O := O)).cost s ≤ 60*(budget+1) := by
  have setup := proposalSetup_bound (O := O) s budget sizes
  have finish := proposalFinish_bound (O := O) ((proposalSetup (O := O)).eval s) budget setup.1
  refine ⟨finish.1,?_⟩
  change (proposalSetup (O := O)).cost s+1+(proposalFinish (O := O)).cost ((proposalSetup (O := O)).eval s) ≤ _
  omega

end ComplexityOfGenerators.Simulation.StarPaths
