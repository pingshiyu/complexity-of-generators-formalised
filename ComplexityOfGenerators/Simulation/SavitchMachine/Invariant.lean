import ComplexityOfGenerators.Simulation.SavitchMachine.Program

/-! The midpoint width is preserved exactly. Complexitylib's existing stack
size invariant bounds field lengths, whereas the child constructor also needs
the exact width when it initializes the all-zero midpoint. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Complexity

def MidpointWidth (width : ℕ) (fs : List Sav.Frm) : Prop :=
  ∀ f ∈ fs, f.m.length = width

@[simp] theorem midpointWidth_nil (width : ℕ) : MidpointWidth width [] := by
  simp [MidpointWidth]

@[simp] theorem midpointWidth_cons (width : ℕ) (f : Sav.Frm) (fs : List Sav.Frm) :
    MidpointWidth width (f :: fs) ↔ f.m.length = width ∧ MidpointWidth width fs := by
  simp [MidpointWidth]

@[simp] theorem child_midpoint (z : List Bool) (f : Sav.Frm) : (Sav.child z f).m = z := by
  simp only [Sav.child]; split <;> first | rfl | (split <;> rfl)

theorem step_midpointWidth (br : List Bool → List Bool → Bool) (ba : List Bool → Bool)
    (z : List Bool) (width : ℕ) (zero : z.length = width) (s : Sav.Sst)
    (size : MidpointWidth width s.stk) : MidpointWidth width (Sav.step br ba z s).stk := by
  rcases s with ⟨done, answer, returned, stk⟩
  cases done with
  | true => exact size
  | false =>
      cases stk with
      | nil => simp [Sav.step]
      | cons f fs =>
          obtain ⟨head, tail⟩ := (midpointWidth_cons width f fs).mp size
          cases returned with
          | none =>
              by_cases level : f.lvl = []
              · simpa [Sav.step, level] using tail
              · simpa [Sav.step, level, head, zero] using (midpointWidth_cons width f fs).mpr ⟨head, tail⟩
          | some result =>
              cases result with
              | false =>
                  cases overflow : bumpOver f.m <;> simp [Sav.step, overflow, head, tail]
              | true => cases phase : f.ph <;> simp [Sav.step, phase, head, tail]

theorem iterate_midpointWidth (br : List Bool → List Bool → Bool) (ba : List Bool → Bool)
    (z : List Bool) (width : ℕ) (zero : z.length = width) (s : Sav.Sst)
    (size : MidpointWidth width s.stk) (steps : ℕ) :
    MidpointWidth width ((Sav.step br ba z)^[steps] s).stk := by
  induction steps with
  | zero => exact size
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact step_midpointWidth br ba z width zero _ ih

end ComplexityOfGenerators.Simulation.SavitchMachine
