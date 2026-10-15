import ComplexityOfGenerators.Simulation.SavitchMachine.Execution
import ComplexityOfGenerators.Simulation.StackSpace.Extend

/-! The recursive interpreter with a thirteenth, persistent input stack.
Recursive routines cannot change this stack. The graph-test subprogram can
read it and must restore it, along with the frame-layout invariant. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.WithInput

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

variable {B : Type}

abbrev Code (B : Type) := Stmt Symbol (Label B) Local 12

def program (baseEntry : B) (base : B → Code B) : Label B → Code B
  | .base pc => base pc
  | q => extendCode (SavitchMachine.program baseEntry (fun _ => .halt) q)

def encoded (input : List Symbol) (q : Label B) (s : Sav.Sst) : Source Symbol (Label B) Local 12 :=
  extendConfig input (SavitchMachine.encoded q s)

variable (baseEntry : B) (base : B → Code B)

/-- Lift any active-ending recursive trace. Placeholder base labels in the
source program halt, hence are never executed by such a trace. -/
theorem lift_trace {r : ℕ} {a b : Source Symbol (Label B) Local 11}
    (trace : Trace (SavitchMachine.program baseEntry (fun _ => .halt)) r a b)
    (active : b.l ≠ none) (input : List Symbol) (room : input.length ≤ r) :
    Trace (program baseEntry base) r (extendConfig input a) (extendConfig input b) := by
  apply trace.extend_active active (program baseEntry base) ?_ input room
  intro q nonhalt
  cases q <;> first | rfl | exact False.elim (nonhalt rfl)

theorem encoded_bound (input : List Symbol) (q : Label B) (s : Sav.Sst) (r : ℕ)
    (room : input.length ≤ r) (bound : ∀ j, (column s.stk j).length ≤ r) :
    Within r (encoded input q s) := extend_bound _ input r (memory_bound _ r bound) room

theorem dispatch_step (input : List Symbol) (s : Sav.Sst) :
    TM2.step (program baseEntry base) (encoded input .dispatch s) =
      (TM2.step (SavitchMachine.program baseEntry (fun _ => .halt))
        (SavitchMachine.encoded .dispatch s)).map (extendConfig input) := by
  simp only [encoded, SavitchMachine.encoded, localConfig, extendConfig, TM2.step, program,
    extend_stepAux, Option.map_some]

/-- Configuration tests may use the input stack, but return with the input
unchanged and the just-completed frame removed. -/
def BaseCorrect (input : List Symbol) (br : List Bool → List Bool → Bool)
    (ba : List Bool → Bool) (r : ℕ) : Prop :=
  ∀ (a : Bool) (f : Sav.Frm) (fs : List Sav.Frm), f.lvl = [] →
    (∀ j, (column (f :: fs) j).length ≤ r) →
    Trace (program baseEntry base) r
      (encoded input (.base baseEntry) ⟨false, a, none, f :: fs⟩)
      (encoded input .dispatch ⟨false, a, some (Sav.baseVal br ba f), fs⟩)

theorem step (input : List Symbol) (br : List Bool → List Bool → Bool)
    (ba : List Bool → Bool) (z : List Bool) (s : Sav.Sst) (active : s.done = false)
    (r : ℕ) (room : input.length ≤ r) (baseCorrect : BaseCorrect baseEntry base input br ba r)
    (zero : ∀ f ∈ s.stk, z = List.replicate f.m.length false)
    (before : ∀ j, (column s.stk j).length ≤ r)
    (after : ∀ j, (column (Sav.step br ba z s).stk j).length ≤ r) :
    Trace (program baseEntry base) r (encoded input .dispatch s)
      (encoded input .dispatch (Sav.step br ba z s)) := by
  rcases s with ⟨done, a, returned, stk⟩
  simp only at active
  subst done
  have initial := encoded_bound input (.dispatch : Label B) ⟨false, a, returned, stk⟩ r room before
  cases stk with
  | nil =>
      apply Trace.step initial
        (by rw [dispatch_step, dispatch_empty]; rfl)
      exact .refl _ (encoded_bound input .dispatch _ r room after)
  | cons f fs =>
      cases returned with
      | none =>
          by_cases level : f.lvl = []
          · rw [Sav.step_base br ba z a f fs level]
            exact .step initial (by rw [dispatch_step, dispatch_base _ _ a f fs level]; rfl)
              (baseCorrect a f fs level before)
          · have bound : ∀ j, (column (Sav.child z f :: f :: fs) j).length ≤ r := by
              simpa only [Sav.step_push br ba z a f fs level] using after
            have child := program_child baseEntry (fun _ => .halt) br ba f fs z (zero f (by simp)) a level r bound
            exact .step initial (by rw [dispatch_step, dispatch_child _ _ a f fs level]; rfl)
              (lift_trace baseEntry base child (by simp [SavitchMachine.encoded, localConfig]) input room)
      | some result =>
          cases result with
          | false =>
              have ret := program_return_false baseEntry (fun _ => .halt) br ba z a f fs r before
              exact .step initial (by rw [dispatch_step, dispatch_return]; rfl)
                (lift_trace baseEntry base ret (by simp [SavitchMachine.encoded, localConfig]) input room)
          | true =>
              have ret := program_return_true baseEntry (fun _ => .halt) br ba z a f fs r before
              exact .step initial (by rw [dispatch_step, dispatch_return]; rfl)
                (lift_trace baseEntry base ret (by simp [SavitchMachine.encoded, localConfig]) input room)

theorem iterate (input : List Symbol) (br : List Bool → List Bool → Bool)
    (ba : List Bool → Bool) (z : List Bool) (s : Sav.Sst) (steps r : ℕ)
    (room : input.length ≤ r) (baseCorrect : BaseCorrect baseEntry base input br ba r)
    (zero : ∀ k ≤ steps, ∀ f ∈ ((Sav.step br ba z)^[k] s).stk,
      z = List.replicate f.m.length false)
    (active : ∀ k < steps, ((Sav.step br ba z)^[k] s).done = false)
    (bound : ∀ k ≤ steps, ∀ j, (column ((Sav.step br ba z)^[k] s).stk j).length ≤ r) :
    Trace (program baseEntry base) r (encoded input .dispatch s)
      (encoded input .dispatch ((Sav.step br ba z)^[steps] s)) := by
  induction steps with
  | zero => exact .refl _ (encoded_bound input .dispatch _ r room (bound 0 (by omega)))
  | succ steps ih =>
      have first := ih (fun k hk => zero k (by omega))
        (fun k hk => active k (by omega)) (fun k hk => bound k (by omega))
      have last := step baseEntry base input br ba z ((Sav.step br ba z)^[steps] s)
        (active steps (by omega)) r room baseCorrect (zero steps (by omega)) (bound steps (by omega)) (by
          simpa only [Function.iterate_succ_apply'] using bound (steps + 1) (by omega))
      simpa only [Function.iterate_succ_apply'] using first.trans last

theorem halt (input : List Symbol) (s : Sav.Sst) (done : s.done = true) (r : ℕ)
    (room : input.length ≤ r) (bound : ∀ j, (column s.stk j).length ≤ r) :
    Trace (program baseEntry base) r (encoded input .dispatch s)
      (extendConfig input ⟨none, (status s, none), memory s.stk (fun _ => [])⟩) := by
  have next : TM2.step (program baseEntry base) (encoded input .dispatch s) =
      some (extendConfig input ⟨none, (status s, none), memory s.stk (fun _ => [])⟩) := by
    rw [dispatch_step]
    simp [TM2.step, SavitchMachine.encoded, localConfig, SavitchMachine.program,
      dispatchCode, TM2.stepAux, status, done]
  exact .step (encoded_bound input .dispatch s r room bound) next
    (.refl _ (extend_bound _ input r (memory_bound _ r bound) room))

end ComplexityOfGenerators.Simulation.SavitchMachine.WithInput
