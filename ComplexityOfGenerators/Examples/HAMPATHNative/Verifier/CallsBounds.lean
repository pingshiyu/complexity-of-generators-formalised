import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Calls
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem transfer_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget)
    (src dst : Fin 64) (different : src ≠ dst) (empty : s dst = []) :
    StoreBound ((Routine.transfer (O := Unit) src dst different id).eval s) budget := by
  change StoreBound (Function.update (Function.update s src []) dst ((s src).reverse.map id ++ s dst)) budget
  exact (sizes.clear src).update dst _ (by simpa [empty] using sizes src)

theorem argsSetup_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (argsSetup.eval s) budget ∧ argsSetup.cost s ≤ 300 * (budget + 1) := by
  let a := (Routine.clearMany (O := Unit) lowRegisters).eval s
  let b := (Routine.assign (O := Unit) 32 37 38 (by decide) (by decide) (by decide) id).eval a
  let c := (Routine.transfer (O := Unit) 37 0 (by decide) id).eval b
  let d := (Routine.assign (O := Unit) 36 37 38 (by decide) (by decide) (by decide) id).eval c
  have aBound : StoreBound a budget := sizes.clearMany lowRegisters
  have bBound : StoreBound b budget := aBound.assign 32 37 38 (by decide) (by decide) (by decide) id
  have zero : b 0 = [] := by simp [b, a, Routine.assign_eval, Routine.clearMany_eval, lowRegisters]
  have cBound : StoreBound c budget := transfer_bound b budget bBound 37 0 (by decide) zero
  have dBound : StoreBound d budget := cBound.assign 36 37 38 (by decide) (by decide) (by decide) id
  have one : d 1 = [] := by simp [d, c, b, a, Routine.assign_eval, Routine.transfer, Routine.clearMany_eval, lowRegisters]
  have result := transfer_bound d budget dBound 37 1 (by decide) one
  refine ⟨result, ?_⟩
  have first := Routine.clearMany_cost (O := Unit) lowRegisters s budget (fun j _ => sizes j)
  have count : lowRegisters.length ≤ 64 := (List.length_filter_le _ _).trans (by simp)
  have assign1 : (Routine.assign (O := Unit) 32 37 38 (by decide) (by decide) (by decide) id).cost a ≤ 20 * budget + 3 := by
    rw [Routine.assign_cost]; have := aBound 37; have := aBound 38; have := aBound 32; omega
  have transfer1 : (Routine.transfer (O := Unit) 37 0 (by decide) id).cost b ≤ 6 * budget := by exact Nat.mul_le_mul_left 6 (bBound 37)
  have assign2 : (Routine.assign (O := Unit) 36 37 38 (by decide) (by decide) (by decide) id).cost c ≤ 20 * budget + 3 := by
    rw [Routine.assign_cost]; have := cBound 37; have := cBound 38; have := cBound 36; omega
  have transfer2 : (Routine.transfer (O := Unit) 37 1 (by decide) id).cost d ≤ 6 * budget := by exact Nat.mul_le_mul_left 6 (dBound 37)
  change (Routine.clearMany (O := Unit) lowRegisters).cost s + 1 +
    ((Routine.assign (O := Unit) 32 37 38 (by decide) (by decide) (by decide) id).cost a + 1 +
      ((Routine.transfer (O := Unit) 37 0 (by decide) id).cost b + 1 +
        ((Routine.assign (O := Unit) 36 37 38 (by decide) (by decide) (by decide) id).cost c + 1 +
          (Routine.transfer (O := Unit) 37 1 (by decide) id).cost d))) ≤ _
  nlinarith only [first, count, assign1, transfer1, assign2, transfer2]

theorem rename_bound (body : Routine Symbol Unit 32) (s : Store) (budget : ℕ)
    (ambient : StoreBound s budget) (owned : StoreBound (body.eval (s ∘ slots)) budget) :
    StoreBound ((body.rename slots).eval s) budget := by
  intro j
  by_cases low : j.val < 32
  · let i : Fin 32 := ⟨j.val, low⟩
    have same : slots i = j := Fin.ext rfl
    rw [← same, Routine.rename_eval_here]
    exact owned i
  · have high : 32 ≤ j.val := by omega
    have outside : ∀ i, j ≠ slots i := by
      intro i same
      have equality := congrArg (fun x : Fin 64 => x.val) same
      change j.val = i.val at equality
      have := i.isLt
      omega
    rw [Routine.rename_eval_frame body slots s j outside]
    exact ambient j

theorem invoke_bound (body : Routine Symbol Unit 32) (result : Fin 32)
    (output : Fin 64) (high : 32 ≤ output.val) (scratch : output ≠ 40)
    (s : Store) (budget time : ℕ) (sizes : StoreBound s budget)
    (source : StoreBound (body.eval (Reduction.loadedStore (s 32) (s 36))) budget)
    (clock : body.cost (Reduction.loadedStore (s 32) (s 36)) ≤ time) :
    StoreBound ((invoke body result output high scratch).eval s) budget ∧
      (invoke body result output high scratch).cost s ≤ time + 400 * (budget + 1) := by
  unfold invoke
  let a := argsSetup.eval s
  let b := (body.rename slots).eval a
  obtain ⟨aBound, aCost⟩ := argsSetup_bound s budget sizes
  have owned : StoreBound (body.eval (a ∘ slots)) budget := by rwa [argsSetup_owned]
  have bBound : StoreBound b budget := rename_bound body a budget aBound owned
  have timeBound : (body.rename slots).cost a ≤ time := by simpa only [Routine.rename_cost, a, argsSetup_owned] using clock
  have sd : slots result ≠ output := by
    intro same
    have equality := congrArg (fun x : Fin 64 => x.val) same
    change result.val = output.val at equality
    have := result.isLt
    omega
  have st : slots result ≠ (40 : Fin 64) := by
    intro same
    have equality := congrArg (fun x : Fin 64 => x.val) same
    change result.val = 40 at equality
    have := result.isLt
    omega
  have endBound := bBound.assign (O := Unit) (slots result) output 40 sd st scratch id
  refine ⟨endBound, ?_⟩
  have endCost : (Routine.assign (O := Unit) (slots result) output 40 sd st scratch id).cost b ≤ 20 * budget + 3 := by
    rw [Routine.assign_cost]; have := bBound output; have := bBound 40; have := bBound (slots result); omega
  change argsSetup.cost s + 1 + ((body.rename slots).cost a + 1 + (Routine.assign (O := Unit) (slots result) output 40 sd st scratch id).cost b) ≤ _
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
