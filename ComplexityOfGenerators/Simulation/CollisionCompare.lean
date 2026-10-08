import ComplexityOfGenerators.Simulation.CollisionHashFetch

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

/-- The final comparison reads both stored words and rejects different
lengths as well as different bits. Its bound includes the end-marker test. -/
theorem collision_compare (word : BitString) (xs ys : BitString) (offset : ℕ)
    (c : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7)
    (state : c.state = .compareLeft) (bound : c.inputHead ≤ word.length)
    (head₁ : c.head 5 = (offset : ℤ)) (head₂ : c.head 6 = (offset : ℤ))
    (left : ∀ i : ℕ, c.tape 5 ((offset + i : ℕ) : ℤ) = collisionWord M xs i)
    (right : ∀ i : ℕ, c.tape 6 ((offset + i : ℕ) : ℤ) = collisionWord M ys i) :
    ∃ t, t ≤ 2 * xs.length + 1 ∧ (collisionBank M).Executes word c t (decide (xs = ys)) := by
  induction xs generalizing ys offset c with
  | nil =>
      have leftZero : c.tape 5 (offset : ℤ) = collisionBlank M := by simpa using left 0
      let d : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
        {c with state := .compareRight none, head := Function.update c.head 5 (offset + 1)}
      have action : (collisionBank M).instruction word c =
          .step (.compareRight none) (c.tape 5 (c.head 5)) .right .stay := by
        simp [TapeBank.instruction, collisionBank, state, collisionSelect, collisionTransition,
          head₁, leftZero, collisionBlank]
      have first := TapeBank.Steps.single (collisionBank M) word c _ _ .right .stay action
      have adv := TapeBank.advance_read (collisionBank M) word c (.compareRight none) .right bound
      simp only [show (collisionBank M).select c.state = 5 by simp [collisionBank, state, collisionSelect]] at adv
      rw [adv] at first
      have first' : (collisionBank M).Steps word c 1 d := by simpa [d, Move.onInt, head₁] using first
      have rightZero := right 0
      cases ys with
      | nil =>
          refine ⟨1, by simp, ?_⟩
          apply first'.executes (collisionBank M) (t := 0)
          apply TapeBank.Executes.accept
          simp [TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition,
            head₂, show c.tape 6 (offset : ℤ) = collisionBlank M by simpa using rightZero, collisionBlank]
      | cons b bs =>
          refine ⟨1, by simp, ?_⟩
          apply first'.executes (collisionBank M) (t := 0)
          apply TapeBank.Executes.reject
          simp [TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition,
            head₂, show c.tape 6 (offset : ℤ) = collisionBit M b by simpa [collisionBit, collisionWord] using rightZero,
            collisionBit]
  | cons a xs ih =>
      have leftZero : c.tape 5 (offset : ℤ) = collisionBit M a := by simpa [collisionBit, collisionWord] using left 0
      let d : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
        {c with state := .compareRight (some a), head := Function.update c.head 5 (offset + 1)}
      have action : (collisionBank M).instruction word c =
          .step (.compareRight (some a)) (c.tape 5 (c.head 5)) .right .stay := by
        simp [TapeBank.instruction, collisionBank, state, collisionSelect, collisionTransition,
          head₁, leftZero, collisionBit]
      have first := TapeBank.Steps.single (collisionBank M) word c _ _ .right .stay action
      have adv := TapeBank.advance_read (collisionBank M) word c (.compareRight (some a)) .right bound
      simp only [show (collisionBank M).select c.state = 5 by simp [collisionBank, state, collisionSelect]] at adv
      rw [adv] at first
      have first' : (collisionBank M).Steps word c 1 d := by simpa [d, Move.onInt, head₁] using first
      have rightZero := right 0
      cases ys with
      | nil =>
          refine ⟨1, by simp, ?_⟩
          apply first'.executes (collisionBank M) (t := 0)
          apply TapeBank.Executes.reject
          simp [TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition,
            head₂, show c.tape 6 (offset : ℤ) = collisionBlank M by simpa using rightZero, collisionBlank]
      | cons b ys =>
          have rightCell : c.tape 6 (offset : ℤ) = collisionBit M b := by simpa [collisionBit, collisionWord] using rightZero
          by_cases same : a = b
          · subst b
            let e := {d with
              state := CollisionPhase.compareLeft (states := M.states) (symbols := M.symbols)
              head := Function.update d.head 6 (offset + 1)}
            have action' : (collisionBank M).instruction word d =
                .step .compareLeft (d.tape 6 (d.head 6)) .right .stay := by
              simp [TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition,
                head₂, rightCell, collisionBit]
            have second := TapeBank.Steps.single (collisionBank M) word d _ _ .right .stay action'
            have adv' := TapeBank.advance_read (collisionBank M) word d .compareLeft .right bound
            simp only [show (collisionBank M).select d.state = 6 by rfl] at adv'
            rw [adv'] at second
            have second' : (collisionBank M).Steps word d 1 e := by
              simpa [e, d, head₂, Move.onInt] using second
            have head₁' : e.head 5 = ((offset + 1 : ℕ) : ℤ) := by simp [e, d]
            have head₂' : e.head 6 = ((offset + 1 : ℕ) : ℤ) := by simp [e]
            have left' (i : ℕ) : e.tape 5 ((offset + 1 + i : ℕ) : ℤ) = collisionWord M xs i := by
              have read := left (i + 1)
              simpa [e, d, collisionWord, show (0 : ℤ) ≤ (i : ℤ) + 1 by omega,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using read
            have right' (i : ℕ) : e.tape 6 ((offset + 1 + i : ℕ) : ℤ) = collisionWord M ys i := by
              have read := right (i + 1)
              simpa [e, d, collisionWord, show (0 : ℤ) ≤ (i : ℤ) + 1 by omega,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using read
            obtain ⟨t, cost, run⟩ := ih ys (offset + 1) e rfl bound head₁' head₂' left' right'
            refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
            simpa using (first'.trans (collisionBank M) second').executes (collisionBank M) run
          · refine ⟨1, by simp, ?_⟩
            have run : (collisionBank M).Executes word d 0 false := by
              apply TapeBank.Executes.reject
              simp [TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition,
                head₂, rightCell, collisionBit, same]
            simpa [same] using first'.executes (collisionBank M) run

end
end ComplexityOfGenerators.Simulation
