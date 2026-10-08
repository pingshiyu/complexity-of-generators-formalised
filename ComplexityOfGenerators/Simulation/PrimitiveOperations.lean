import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Sum
import ComplexityOfGenerators.Machine

/-! Primitive recursiveness of tape-head movement under Mathlib's standard
integer encoding. The encoding is reused, rather than assumed computable. -/

namespace ComplexityOfGenerators.Simulation

theorem primrec_int_code : Primrec Equiv.intEquivNat :=
  Primrec.encode.of_eq fun _ => rfl

theorem primrec_int_decode : Primrec Equiv.intEquivNat.symm :=
  (Primrec.ofNat ℤ).of_eq fun _ => rfl

def leftIntegerCode (n : ℕ) : ℕ :=
  if n.bodd then n + 2 else if n = 0 then 1 else n - 2

def rightIntegerCode (n : ℕ) : ℕ :=
  if n.bodd then if n = 1 then 0 else n - 2 else n + 2

theorem primrec_leftIntegerCode : Primrec leftIntegerCode := by
  have code := Primrec.cond Primrec.nat_bodd
    (Primrec.nat_add.comp .id (.const 2))
    (Primrec.ite (Primrec.eq.comp .id (.const 0)) (.const 1)
      (Primrec.nat_sub.comp .id (.const 2)))
  exact code.of_eq fun n => by simp [leftIntegerCode, Bool.cond_eq_ite]

theorem primrec_rightIntegerCode : Primrec rightIntegerCode := by
  have code := Primrec.cond Primrec.nat_bodd
    (Primrec.ite (Primrec.eq.comp .id (.const 1)) (.const 0)
      (Primrec.nat_sub.comp .id (.const 2)))
    (Primrec.nat_add.comp .id (.const 2))
  exact code.of_eq fun n => by simp [rightIntegerCode, Bool.cond_eq_ite]

theorem leftIntegerCode_correct (i : ℤ) :
    leftIntegerCode (Equiv.intEquivNat i) = Equiv.intEquivNat (i - 1) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
          have movement : Int.ofNat (n + 1) - 1 = Int.ofNat n := by
            change ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ)
            omega
          rw [movement]
          change leftIntegerCode (2 * (n + 1)) = 2 * n
          simp [leftIntegerCode, Nat.bodd_mul]
          omega
  | negSucc n =>
      have movement : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
      rw [movement]
      change leftIntegerCode (2 * n + 1) = 2 * (n + 1) + 1
      simp [leftIntegerCode, Nat.bodd_mul]
      omega

theorem rightIntegerCode_correct (i : ℤ) :
    rightIntegerCode (Equiv.intEquivNat i) = Equiv.intEquivNat (i + 1) := by
  cases i with
  | ofNat n =>
      have movement : Int.ofNat n + 1 = Int.ofNat (n + 1) := by
        change (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)
        omega
      rw [movement]
      change rightIntegerCode (2 * n) = 2 * (n + 1)
      simp [rightIntegerCode, Nat.bodd_mul]
      omega
  | negSucc n =>
      cases n with
      | zero => rfl
      | succ n =>
          have movement : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
          rw [movement]
          change rightIntegerCode (2 * (n + 1) + 1) = 2 * n + 1
          simp [rightIntegerCode, Nat.bodd_mul]
          omega

theorem primrec_int_left : Primrec (fun i : ℤ => i - 1) :=
  (primrec_int_decode.comp (primrec_leftIntegerCode.comp primrec_int_code)).of_eq fun i => by
    rw [leftIntegerCode_correct]
    exact Equiv.intEquivNat.symm_apply_apply (i - 1)

theorem primrec_int_right : Primrec (fun i : ℤ => i + 1) :=
  (primrec_int_decode.comp (primrec_rightIntegerCode.comp primrec_int_code)).of_eq fun i => by
    rw [rightIntegerCode_correct]
    exact Equiv.intEquivNat.symm_apply_apply (i + 1)

def moveEquiv : Move ≃ (Unit ⊕ Bool) where
  toFun
    | .left => .inl ()
    | .stay => .inr false
    | .right => .inr true
  invFun
    | .inl _ => .left
    | .inr false => .stay
    | .inr true => .right
  left_inv m := by cases m <;> rfl
  right_inv m := by
    cases m with
    | inl u => cases u; rfl
    | inr b => cases b <;> rfl

instance : Primcodable Move := Primcodable.ofEquiv (Unit ⊕ Bool) moveEquiv

instance : Finite Move := Finite.of_injective moveEquiv moveEquiv.injective

theorem primrec_move_onInt : Primrec₂ Move.onInt := by
  have step : Primrec (fun p : Move × ℤ =>
      if p.1 = .left then p.2 - 1 else if p.1 = .right then p.2 + 1 else p.2) :=
    Primrec.ite (Primrec.eq.comp .fst (.const Move.left)) (primrec_int_left.comp .snd)
      (Primrec.ite (Primrec.eq.comp .fst (.const Move.right)) (primrec_int_right.comp .snd) .snd)
  exact step.of_eq fun ⟨m, i⟩ => by cases m <;> rfl

theorem primrec_move_onInput : Primrec (fun p : Move × ℕ × ℕ => p.1.onInput p.2.1 p.2.2) := by
  have step : Primrec (fun p : Move × ℕ × ℕ =>
      if p.1 = .left then p.2.2 - 1
      else if p.1 = .right then min (p.2.2 + 1) p.2.1 else min p.2.2 p.2.1) :=
    Primrec.ite (Primrec.eq.comp .fst (.const Move.left))
      (Primrec.nat_sub.comp (Primrec.snd.comp .snd) (.const 1))
      (Primrec.ite (Primrec.eq.comp .fst (.const Move.right))
        (Primrec.nat_min.comp (Primrec.succ.comp (Primrec.snd.comp .snd)) (Primrec.fst.comp .snd))
        (Primrec.nat_min.comp (Primrec.snd.comp .snd) (Primrec.fst.comp .snd)))
  exact step.of_eq fun ⟨m, bound, i⟩ => by cases m <;> rfl

end ComplexityOfGenerators.Simulation
