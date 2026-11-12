import ComplexityOfGenerators.Simulation.StarPaths.DPBounds
import ComplexityOfGenerators.Simulation.StarPaths.ProposalBounds
import ComplexityOfGenerators.Simulation.StarPaths.ValidationBounds
import ComplexityOfGenerators.Simulation.StarPaths.Native

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem saveFallback_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((saveFallback (O := O)).eval s) budget ∧
      (saveFallback (O := O)).cost s ≤ 50*(budget+1) := by
  constructor
  · exact (sizes.assign 10 14 12 (by decide) (by decide) (by decide) id).assign
      11 15 12 (by decide) (by decide) (by decide) id
  · have a := sizes 10
    have b := sizes 11
    have c := sizes 12
    have d := sizes 14
    have e := sizes 15
    simp [saveFallback,WordStack.Routine.seq,WordStack.Routine.assign_cost,WordStack.Routine.assign_eval]
    omega

theorem selectResult_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((selectResult (O := O)).eval s) (budget+1) ∧
      (selectResult (O := O)).cost s ≤ 50*(budget+1) := by
  by_cases available : (s 20).head?.isSome = true
  · simp only [selectResult,WordStack.Routine.branch,available,ite_true]
    constructor
    · have value : ((WordStack.Routine.clear (O := O) 32).seq
          (WordStack.Routine.ofLocal (Local.push 32 Symbol.present))).eval s = Function.update s 32 [Symbol.present] := by
        simp [WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push]
      rw [value]
      exact (sizes.mono (by omega)).update 32 _ (by simp)
    · have := sizes 32
      simp [WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.push,Local.ticks]
      omega
  · simp only [selectResult,WordStack.Routine.branch,available,Bool.false_eq_true,ite_false]
    constructor
    · exact ((sizes.assign 14 31 12 (by decide) (by decide) (by decide) id).assign
        15 32 12 (by decide) (by decide) (by decide) id).mono (by omega)
    · have a := sizes 14
      have b := sizes 15
      have c := sizes 12
      have d := sizes 31
      have e := sizes 32
      simp [WordStack.Routine.seq,WordStack.Routine.assign_cost,WordStack.Routine.assign_eval]
      omega

def dpBudget (initial target : ℕ) : ℕ := initial+1+target*(target+3)^2

def pathBudget (initial target : ℕ) : ℕ := 3*dpBudget initial target+4

def pathTime (initial target : ℕ) : ℕ :=
  200*(initial+1)+1+target*(1000*(target+3)^3+4)*(dpBudget initial target+1)+
    10000*(dpBudget initial target+2)^2

/-- A polynomial bound for every instruction and stored word of the complete
native path selector, including initial caller garbage and both proposals. -/
theorem pathRoutine_bound {O : Type} (flags : List Bool) (s : Store) (initial target : ℕ)
    (sizes : StoreBound s initial) (source : s 25 = flagsWord flags) (master : (s 22).length = target) :
    StoreBound ((pathRoutine (O := O)).eval s) (pathBudget initial target) ∧
      (pathRoutine (O := O)).cost s ≤ pathTime initial target := by
  let dynamic := (dpRoutine (O := O)).eval s
  let cached := (saveFallback (O := O)).eval dynamic
  let proposed := (proposalRoutine (O := O)).eval cached
  let checked := (validationRoutine (O := O)).eval proposed
  have dp := dpRoutine_bound (O := O) flags s initial target sizes source master
  have dpSize : StoreBound dynamic (dpBudget initial target) := dp.1
  have saved := saveFallback_bound (O := O) dynamic (dpBudget initial target) dpSize
  have proposal := proposalRoutine_bound (O := O) cached (dpBudget initial target) saved.1
  have validation := validationRoutine_bound (O := O) proposed (3*dpBudget initial target+2) proposal.1
  have selected := selectResult_bound (O := O) checked (3*dpBudget initial target+2+1) validation.1
  constructor
  · exact selected.1.mono (by unfold pathBudget; omega)
  · change (dpRoutine (O := O)).cost s+1+((saveFallback (O := O)).cost dynamic+1+
      ((proposalRoutine (O := O)).cost cached+1+((validationRoutine (O := O)).cost proposed+1+
        (selectResult (O := O)).cost checked))) ≤ _
    have saveCost := saved.2
    have proposalCost := proposal.2
    have validationCost := validation.2
    have selectedCost := selected.2
    have afterCost : 1+(saveFallback (O := O)).cost dynamic+1+
        ((proposalRoutine (O := O)).cost cached+1+((validationRoutine (O := O)).cost proposed+1+
          (selectResult (O := O)).cost checked)) ≤ 10000*(dpBudget initial target+2)^2 := by
      nlinarith
    have dpCost := dp.2
    change (dpRoutine (O := O)).cost s ≤
      200*(initial+1)+1+target*(1000*(target+3)^3+4)*(dpBudget initial target+1) at dpCost
    unfold pathTime
    omega

private noncomputable def dpPolynomial (initial : PolynomialBound) : Polynomial ℕ :=
  initial.asPolynomial+1+Polynomial.X*(Polynomial.X+3)^2

noncomputable def workspace (initial : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (3*dpPolynomial initial+4)

noncomputable def primitiveTime (initial : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (200*(initial.asPolynomial+1)+1+
      Polynomial.X*(1000*(Polynomial.X+3)^3+4)*(dpPolynomial initial+1)+10000*(dpPolynomial initial+2)^2)

private theorem dpPolynomial_eval (initial : PolynomialBound) (n : ℕ) :
    (dpPolynomial initial).eval n = dpBudget (initial n) n := by
  simp [dpPolynomial,dpBudget,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval]

theorem pathRoutine_resources {O : Type} (initial : PolynomialBound) (flags : List Bool) (s : Store) (n : ℕ)
    (sizes : StoreBound s (initial n)) (source : s 25 = flagsWord flags) (master : (s 22).length = n) :
    StoreBound ((pathRoutine (O := O)).eval s) (workspace initial n) ∧
      (pathRoutine (O := O)).cost s ≤ primitiveTime initial n := by
  have raw := pathRoutine_bound (O := O) flags s (initial n) n sizes source master
  constructor
  · apply raw.1.mono
    have lower := PolynomialBound.eval_le_ofPolynomial (3*dpPolynomial initial+4) n
    simpa [workspace,pathBudget,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,dpPolynomial_eval] using lower
  · apply raw.2.trans
    have lower := PolynomialBound.eval_le_ofPolynomial
      (200*(initial.asPolynomial+1)+1+Polynomial.X*(1000*(Polynomial.X+3)^3+4)*(dpPolynomial initial+1)+
        10000*(dpPolynomial initial+2)^2) n
    simpa [primitiveTime,pathTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval,dpPolynomial_eval] using lower

end ComplexityOfGenerators.Simulation.StarPaths
