import ComplexityOfGenerators.Simulation.WordStack.Zipper

/-! The two-stack work tape denotes a genuine two-way infinite tape. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Zipper

variable {A : Type}

def cell (blank : A) (z : Zipper A) (i : ℤ) : A :=
  if 0 ≤ i then z.right[i.toNat]?.getD blank else z.left[(-i - 1).toNat]?.getD blank

@[simp] theorem cell_nat (blank : A) (z : Zipper A) (n : ℕ) :
    z.cell blank (n : ℤ) = z.right[n]?.getD blank := by simp [cell]

@[simp] theorem cell_neg (blank : A) (z : Zipper A) (n : ℕ) :
    z.cell blank (Int.negSucc n) = z.left[n]?.getD blank := by
  have negative : ¬(0 ≤ Int.negSucc n) := by omega
  have idx : -Int.negSucc n - 1 = (n : ℤ) := by omega
  simp [cell, negative, idx]

theorem cell_zero (blank : A) (z : Zipper A) : z.cell blank 0 = z.right.head?.getD blank := by
  rw [show (0 : ℤ) = (0 : ℕ) from rfl, cell_nat]
  cases z.right <;> rfl

theorem cell_workMove (blank : A) (z : Zipper A) (direction : Move) (i : ℤ) :
    (z.workMove blank direction).cell blank i = z.cell blank (direction.onInt i) := by
  cases direction with
  | stay => rfl
  | left =>
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        simp [workMove, Move.onInt, cell, List.head?_eq_getElem?]
      | succ n =>
        have shift : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
        change (z.workMove blank .left).cell blank ((n + 1 : ℕ) : ℤ) =
          z.cell blank (((n + 1 : ℕ) : ℤ) - 1)
        rw [shift, cell_nat, cell_nat]
        simp [workMove]
    | negSucc n =>
      have shift : (Int.negSucc n) - 1 = Int.negSucc (n + 1) := by omega
      simp only [Move.onInt, shift, cell_neg, workMove, List.getElem?_tail]
  | right =>
    cases i with
    | ofNat n =>
      have shift : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      change (z.workMove blank .right).cell blank (n : ℤ) = z.cell blank ((n : ℤ) + 1)
      rw [shift, cell_nat, cell_nat]
      simp [workMove, List.getElem?_tail]
    | negSucc n =>
      cases n with
      | zero =>
        simp [workMove, Move.onInt, cell, List.head?_eq_getElem?]
      | succ n =>
        have shift : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
        simp only [Move.onInt, shift, cell_neg, workMove, List.getElem?_cons_succ]

theorem cell_write (blank a : A) (z : Zipper A) (i : ℤ) :
    (z.write a).cell blank i = if i = 0 then a else z.cell blank i := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => simp [cell, write]
    | succ n =>
      change (z.write a).cell blank ((n + 1 : ℕ) : ℤ) =
        if ((n + 1 : ℕ) : ℤ) = 0 then a else z.cell blank ((n + 1 : ℕ) : ℤ)
      have ne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
      rw [if_neg ne, cell_nat, cell_nat]
      simp [write, List.getElem?_tail]
  | negSucc n => simp [write]

theorem workMove_absolute (blank : A) (z : Zipper A) (direction : Move) (head i : ℤ) :
    (z.workMove blank direction).cell blank (i - direction.onInt head) = z.cell blank (i - head) := by
  rw [cell_workMove]
  congr 1
  cases direction <;> simp [Move.onInt] <;> ring

theorem write_absolute (blank a : A) (z : Zipper A) (head : ℤ) :
    (fun i => (z.write a).cell blank (i - head)) =
      Function.update (fun i => z.cell blank (i - head)) head a := by
  funext i
  rw [cell_write]
  by_cases equal : i = head
  · subst i; simp
  · simp [equal, show i - head ≠ 0 by omega]

end ComplexityOfGenerators.Simulation.WordStack.Zipper
