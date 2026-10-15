import ComplexityOfGenerators.Simulation.SavitchMachine.Invariant

/-! Bounded execution of the complete recursive control flow. The only
program-specific premise is the depth-zero graph test; recursive calls,
returns, enumeration, termination, and their scratch space are handled here. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

variable {B : Type} (baseEntry : B) (base : B → Stmt Symbol (Label B) Local 11)
variable (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)

/-- A base-test implementation must compute the actual graph predicate,
pop the completed frame, and clear its temporary registers. This is an
implementation obligation, not an assumption in the main complexity theorem. -/
def BaseCorrect (r : ℕ) : Prop :=
  ∀ (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm), f.lvl = [] →
    (∀ j, (column (f :: fs) j).length ≤ r) →
    Trace (program baseEntry base) r
      (encoded (.base baseEntry) ⟨false, a, none, f :: fs⟩)
      (encoded .dispatch ⟨false, a, some (Sav.baseVal br ba f), fs⟩)

/-- One recursive interpreter step executes inside the common stack bound.
Both endpoint bounds are used: descent may add one frame. -/
theorem program_step (s : Sav.Sst) (active : s.done = false) (r : ℕ)
    (baseCorrect : BaseCorrect baseEntry base br ba r)
    (zero : ∀ f ∈ s.stk, z = List.replicate f.m.length false)
    (before : ∀ j, (column s.stk j).length ≤ r)
    (after : ∀ j, (column (Sav.step br ba z s).stk j).length ≤ r) :
    Trace (program baseEntry base) r (encoded .dispatch s)
      (encoded .dispatch (Sav.step br ba z s)) := by
  rcases s with ⟨done, a, returned, stk⟩
  simp only at active
  subst done
  cases stk with
  | nil =>
      exact .step (memory_bound _ r before) (dispatch_empty baseEntry base a returned)
        (.refl _ (memory_bound _ r after))
  | cons f fs =>
      cases returned with
      | none =>
          by_cases level : f.lvl = []
          · have path := baseCorrect a f fs level before
            have next := dispatch_base baseEntry base a f fs level
            rw [Sav.step_base br ba z a f fs level]
            exact .step (memory_bound _ r before) next path
          · have next := dispatch_child baseEntry base a f fs level
            have bound : ∀ j, (column (Sav.child z f :: f :: fs) j).length ≤ r := by
              simpa only [Sav.step_push br ba z a f fs level] using after
            exact .step (memory_bound _ r before) next
              (program_child baseEntry base br ba f fs z (zero f (by simp)) a level r bound)
      | some result =>
          cases result with
          | false =>
              exact .step (memory_bound _ r before) (dispatch_return baseEntry base a false f fs)
                (program_return_false baseEntry base br ba z a f fs r before)
          | true =>
              exact .step (memory_bound _ r before) (dispatch_return baseEntry base a true f fs)
                (program_return_true baseEntry base br ba z a f fs r before)

/-- Every finite active prefix of the library interpreter is implemented by
an actual bounded stack-program trace, including all recursive subroutines. -/
theorem program_iterate (s : Sav.Sst) (steps r : ℕ)
    (baseCorrect : BaseCorrect baseEntry base br ba r)
    (zero : ∀ k ≤ steps, ∀ f ∈ ((Sav.step br ba z)^[k] s).stk,
      z = List.replicate f.m.length false)
    (active : ∀ k < steps, ((Sav.step br ba z)^[k] s).done = false)
    (bound : ∀ k ≤ steps, ∀ j, (column ((Sav.step br ba z)^[k] s).stk j).length ≤ r) :
    Trace (program baseEntry base) r (encoded .dispatch s)
      (encoded .dispatch ((Sav.step br ba z)^[steps] s)) := by
  induction steps with
  | zero => exact .refl _ (memory_bound _ r (bound 0 (by omega)))
  | succ steps ih =>
      have first := ih (fun k hk => zero k (by omega))
        (fun k hk => active k (by omega)) (fun k hk => bound k (by omega))
      have last := program_step baseEntry base br ba z ((Sav.step br ba z)^[steps] s)
        (active steps (by omega)) r baseCorrect (zero steps (by omega)) (bound steps (by omega)) (by
          simpa only [Function.iterate_succ_apply'] using bound (steps + 1) (by omega))
      simpa only [Function.iterate_succ_apply'] using first.trans last

/-- Once the library reports completion, the finite program halts with
exactly its answer. The terminal configuration is part of the space bound. -/
theorem program_halt (s : Sav.Sst) (done : s.done = true) (r : ℕ)
    (bound : ∀ j, (column s.stk j).length ≤ r) :
    Trace (program baseEntry base) r (encoded .dispatch s)
      ⟨none, (status s, none), memory s.stk (fun _ => [])⟩ := by
  have next : TM2.step (program baseEntry base) (encoded .dispatch s) =
      some ⟨none, (status s, none), memory s.stk (fun _ => [])⟩ := by
    simp [TM2.step, encoded, localConfig, program, dispatchCode, TM2.stepAux, status, done]
  exact .step (memory_bound _ r bound) next (.refl _ (memory_bound _ r bound))

end ComplexityOfGenerators.Simulation.SavitchMachine
