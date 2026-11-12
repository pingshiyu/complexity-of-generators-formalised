import ComplexityOfGenerators.Simulation.StarPaths.Basic
import ComplexityOfGenerators.Simulation.StarPaths.Proposal

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true

def coinSymbol : Bool → Symbol | false => .bitFalse | true => .bitTrue

def proposalCoin {O : Type} : Step O :=
  (WordStack.Routine.branch 17 fun coin => if coin = some .bitTrue then
    WordStack.Routine.ofLocal (Local.push 31 .cut) else WordStack.Routine.skip).seq
      ((WordStack.Routine.ofLocal (Local.push 31 .unit)).seq (WordStack.Routine.ofLocal (Local.pop 17)))

theorem proposalCoin_frame {O : Type} (j : Fin 35) (a : j ≠ 17) (b : j ≠ 31) :
    (proposalCoin (O := O)).Fixes j := by
  unfold proposalCoin
  apply WordStack.Routine.Fixes.seq
  · apply WordStack.Routine.Fixes.branch
    intro coin
    split_ifs
    · exact WordStack.Routine.fixes_push 31 j Symbol.cut b
    · exact WordStack.Routine.fixes_skip j
  · exact (WordStack.Routine.fixes_push 31 j Symbol.unit b).seq (WordStack.Routine.fixes_pop 17 j a)

def proposalLoop {O : Type} : Step O := WordStack.Routine.iterate 18 proposalCoin
  (proposalCoin_frame 18 (by decide) (by decide))

def proposalSetup {O : Type} : Step O :=
  (WordStack.Routine.clear 31).seq
    ((WordStack.Routine.assign 22 18 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)).seq
      (WordStack.Routine.ofLocal (Local.pop 18)))

def proposalFinish {O : Type} : Step O :=
  WordStack.Routine.branch 22 fun size => if size.isSome then
    (WordStack.Routine.ofLocal (Local.push 31 .unit)).seq
      (proposalLoop.seq (WordStack.Routine.ofLocal (Local.push 31 .cut)))
  else WordStack.Routine.skip

def proposalRoutine {O : Type} : Step O := proposalSetup.seq proposalFinish

private theorem proposalCoin_value {O : Type} (s : Store) :
    (proposalCoin (O := O)).eval s = Function.update (Function.update s 31
      (if (s 17).head? = some .bitTrue then .unit::.cut::s 31 else .unit::s 31)) 17 (s 17).tail := by
  unfold proposalCoin
  by_cases cut : (s 17).head? = some Symbol.bitTrue
  · simp [WordStack.Routine.seq,WordStack.Routine.branch,cut,WordStack.Routine.ofLocal,Local.eval_push,Local.eval_pop]
  · simp [WordStack.Routine.seq,WordStack.Routine.branch,cut,WordStack.Routine.ofLocal,Local.eval_push,Local.eval_pop,
      WordStack.Routine.skip]

/-- Counted native cut steps agree with the explicit tail-recursive cut walk. -/
theorem proposalLoop_counted {O : Type} (count : ℕ) (bits : List Bool) (current : ℕ) (prior : Parts) (s : Store)
    (coins : s 17 = bits.map coinSymbol) (buffer : s 31 = List.replicate current .unit++payload prior) :
    let output := ((WordStack.Routine.counted 18 (proposalCoin (O := O))).eval^[count] s)
    output 17 = (bits.drop count).map coinSymbol ∧
      .cut::output 31 = payload (cutWalk count bits current prior) := by
  induction count generalizing bits current prior s with
  | zero =>
      simp only [Function.iterate_zero,Function.id_def,List.drop_zero,cutWalk]
      exact ⟨coins,by simp [payload,buffer]⟩
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      let ready := (WordStack.Routine.counted 18 (proposalCoin (O := O))).eval s
      have step : ready = (proposalCoin (O := O)).eval (Function.update s 18 (s 18).tail) := rfl
      have contents : ready 17 = bits.tail.map coinSymbol := by
        rw [step,proposalCoin_value]
        simp [coins,List.map_tail]
      have old : (Function.update s 18 (s 18).tail) 31 = s 31 := by simp
      by_cases cut : (bits[0]?).getD false
      · have head : (s 17).head? = some Symbol.bitTrue := by
          cases bits with
          | nil => simp at cut
          | cons bit rest => cases bit <;> simp [coins,coinSymbol] at cut ⊢
        have next : ready 31 = List.replicate 1 .unit++payload (current::prior) := by
          rw [step,proposalCoin_value]
          simp [head,old,buffer,payload]
        have result := ih bits.tail 1 (current::prior) ready contents next
        refine ⟨?_,?_⟩
        · simpa only [List.drop_tail] using result.1
        · simpa only [cutWalk,cut,ite_true] using result.2
      · have head : (s 17).head? ≠ some Symbol.bitTrue := by
          cases bits with
          | nil => simp [coins]
          | cons bit rest => cases bit <;> simp [coins,coinSymbol] at cut ⊢
        have next : ready 31 = List.replicate (current+1) .unit++payload prior := by
          rw [step,proposalCoin_value]
          simp [head,old,buffer,List.replicate_succ]
        have result := ih bits.tail (current+1) prior ready contents next
        refine ⟨?_,?_⟩
        · simpa only [List.drop_tail] using result.1
        · simpa only [cutWalk,cut,Bool.false_eq_true,ite_false] using result.2

end ComplexityOfGenerators.Simulation.StarPaths
