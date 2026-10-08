import ComplexityOfGenerators.Foundations.ResourceBounds
import Mathlib.Data.List.OfFn

/-! Arithmetic for the fixed-degree, radix-`n + 1` clock. Lists here describe
the locations of finitely many tape markers; they are proof-level invariants,
not additional machine instructions or infinite control states. -/

namespace ComplexityOfGenerators.Simulation

def clockLocations {k : ℕ} (digits : List ℕ) (i : Fin k) : Option ℤ :=
  digits[i.val]?.map Int.ofNat

theorem clockLocations_at {k : ℕ} (pre tail : List ℕ) (d : ℕ) (h : pre.length < k) :
    clockLocations (pre ++ d :: tail) (⟨pre.length, h⟩ : Fin k) = some (d : ℤ) := by
  simp [clockLocations]

theorem clockLocations_update {k : ℕ} (pre tail : List ℕ) (d v : ℕ) (h : pre.length < k) :
    clockLocations (k := k) (pre ++ v :: tail) =
      Function.update (clockLocations (pre ++ d :: tail)) ⟨pre.length, h⟩ (some (v : ℤ)) := by
  funext i
  by_cases same : i.val = pre.length
  · have eq : i = ⟨pre.length, h⟩ := Fin.ext same
    subst i
    simp [clockLocations_at]
  · rw [Function.update_of_ne (fun he => same (congrArg Fin.val he))]
    unfold clockLocations
    by_cases before : i.val < pre.length
    · rw [List.getElem?_append_left before, List.getElem?_append_left before]
    · have after : pre.length ≤ i.val := by omega
      rw [List.getElem?_append_right after, List.getElem?_append_right after]
      have positive : 0 < i.val - pre.length := by omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt positive)
      rw [hj]
      rfl

def clockDigitValue (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + (n + 1) * clockDigitValue n ds

def clockDigitIncrement (n : ℕ) : List ℕ → List ℕ × Bool
  | [] => ([], true)
  | d :: ds =>
      if d < n then ((d + 1) :: ds, false)
      else let next := clockDigitIncrement n ds; (0 :: next.1, next.2)

@[simp] theorem clockDigitIncrement_length (n : ℕ) (ds : List ℕ) :
    (clockDigitIncrement n ds).1.length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [clockDigitIncrement]; split <;> simp_all

theorem clockDigitIncrement_bounded (n : ℕ) (ds : List ℕ)
    (bounded : ∀ d ∈ ds, d ≤ n) :
    ∀ d ∈ (clockDigitIncrement n ds).1, d ≤ n := by
  induction ds with
  | nil => simp [clockDigitIncrement]
  | cons d ds ih =>
      have tail : ∀ d ∈ ds, d ≤ n := fun d hd => bounded d (List.mem_cons_of_mem _ hd)
      simp only [clockDigitIncrement]
      split
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact tail x hx
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact ih tail x hx

theorem clockDigitValue_lt (n : ℕ) (ds : List ℕ)
    (bounded : ∀ d ∈ ds, d ≤ n) : clockDigitValue n ds < (n + 1) ^ ds.length := by
  induction ds with
  | nil => simp [clockDigitValue]
  | cons d ds ih =>
      have head := bounded d (by simp)
      have tail := ih (fun d hd => bounded d (List.mem_cons_of_mem _ hd))
      simp only [clockDigitValue, List.length_cons, pow_succ]
      nlinarith

/-- Carry-out contributes exactly one full revolution of the odometer. -/
theorem clockDigitIncrement_value (n : ℕ) (ds : List ℕ)
    (bounded : ∀ d ∈ ds, d ≤ n) :
    clockDigitValue n (clockDigitIncrement n ds).1 +
        (if (clockDigitIncrement n ds).2 then (n + 1) ^ ds.length else 0) =
      clockDigitValue n ds + 1 := by
  induction ds with
  | nil => simp [clockDigitIncrement, clockDigitValue]
  | cons d ds ih =>
      have head := bounded d (by simp)
      have tail := ih (fun d hd => bounded d (List.mem_cons_of_mem _ hd))
      by_cases small : d < n
      · simp [clockDigitIncrement, small, clockDigitValue]
        omega
      · have eq : d = n := by omega
        subst d
        simp only [clockDigitIncrement, lt_self_iff_false, ↓reduceIte,
          clockDigitValue, Nat.zero_add, List.length_cons, pow_succ]
        cases carry : (clockDigitIncrement n ds).2 <;> simp only [carry, Bool.false_eq_true,
          ↓reduceIte, Nat.add_zero] at tail ⊢ <;> nlinarith

theorem clockDigitIncrement_overflow (n : ℕ) (ds : List ℕ)
    (bounded : ∀ d ∈ ds, d ≤ n)
    (overflow : (clockDigitIncrement n ds).2 = true) :
    clockDigitValue n (clockDigitIncrement n ds).1 = 0 ∧
      clockDigitValue n ds + 1 = (n + 1) ^ ds.length := by
  have value := clockDigitIncrement_value n ds bounded
  have less := clockDigitValue_lt n ds bounded
  simp only [overflow, ↓reduceIte] at value
  omega

/-- The natural-valued fuel represented by a positive finite-control block
counter and the digit markers. -/
def clockFuel (n remaining : ℕ) (ds : List ℕ) : ℕ :=
  remaining * (n + 1) ^ ds.length - clockDigitValue n ds

theorem clockFuel_positive (n remaining : ℕ) (ds : List ℕ)
    (positive : 0 < remaining) (bounded : ∀ d ∈ ds, d ≤ n) :
    0 < clockFuel n remaining ds := by
  have value := clockDigitValue_lt n ds bounded
  have mul : (n + 1) ^ ds.length ≤ remaining * (n + 1) ^ ds.length :=
    Nat.le_mul_of_pos_left _ positive
  unfold clockFuel
  omega

theorem clockFuel_increment (n remaining : ℕ) (ds : List ℕ)
    (positive : 0 < remaining) (bounded : ∀ d ∈ ds, d ≤ n) :
    clockFuel n (if (clockDigitIncrement n ds).2 then remaining - 1 else remaining)
        (clockDigitIncrement n ds).1 + 1 = clockFuel n remaining ds := by
  have value := clockDigitIncrement_value n ds bounded
  have oldBound := clockDigitValue_lt n ds bounded
  have mul : (n + 1) ^ ds.length ≤ remaining * (n + 1) ^ ds.length :=
    Nat.le_mul_of_pos_left _ positive
  unfold clockFuel
  rw [clockDigitIncrement_length]
  cases carry : (clockDigitIncrement n ds).2
  · simp only [carry, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at value ⊢
    omega
  · have overflow := clockDigitIncrement_overflow n ds bounded carry
    simp only [↓reduceIte, overflow.1, Nat.sub_zero]
    have product : remaining * (n + 1) ^ ds.length =
        (remaining - 1) * (n + 1) ^ ds.length + (n + 1) ^ ds.length := by
      have r : remaining = remaining - 1 + 1 := by omega
      conv_lhs => rw [r]
      ring
    omega

@[simp] theorem clockDigitValue_zero (n k : ℕ) :
    clockDigitValue n (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, clockDigitValue, ih]

/-- Initializing all markers at the origin gives exactly the approved
polynomial budget, including degree zero and empty inputs. -/
theorem clockFuel_initial (p : PolynomialBound) (n : ℕ) :
    clockFuel n p.coefficient (List.replicate p.degree 0) = p n := by
  simp [clockFuel, PolynomialBound.eval]

end ComplexityOfGenerators.Simulation
