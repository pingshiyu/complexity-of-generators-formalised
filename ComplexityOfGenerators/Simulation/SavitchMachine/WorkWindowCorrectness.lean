import ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindow

/-! Relate the finite-control work-window comparison to decoded tape arrays.
No well-formedness assumption is made on either input bitstring. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindow

set_option backward.isDefEq.respectTransparency false
variable (symbols : ℕ)

def cellsTest (observed : Cell symbols) (write : Option (Fin symbols)) :
    (count : ℕ) → ℕ → Bool → (Fin count → Cell symbols) → (Fin count → Cell symbols) → Bool
  | 0, head, seen, _, _ => seen && decide (head = 0)
  | n + 1, head, seen, a, b =>
      let atHead := !seen && decide (head = 0)
      (!(atHead && decide (a 0 ≠ observed))) &&
      decide (b 0 = if atHead then written symbols write (a 0) else a 0) &&
      cellsTest observed write n (head - 1) (seen || decide (head = 0)) (Fin.tail a) (Fin.tail b)

/-- The bitstream test rejects every malformed window and otherwise applies
exactly the corresponding cell-array test. -/
theorem test_eq_decoded (observed : Cell symbols) (write : Option (Fin symbols))
    (count head : ℕ) (seen : Bool) (u v : List Bool) :
    test symbols observed write count head seen u v =
      (((FixedWidthCodec.optionFin symbols).vector count).decode u).any (fun a =>
        (((FixedWidthCodec.optionFin symbols).vector count).decode v).any (fun b =>
          cellsTest symbols observed write count head seen a b)) := by
  induction count generalizing head seen u v with
  | zero =>
      by_cases hu : u = [] <;> by_cases hv : v = [] <;>
        simp [test, cellsTest, FixedWidthCodec.vector, hu, hv, Bool.and_assoc]
  | succ count ih =>
      have tail := ih (head - 1) (seen || decide (head = 0))
        (u.drop (symbols + 1)) (v.drop (symbols + 1))
      have width : (FixedWidthCodec.optionFin symbols).width = symbols + 1 := rfl
      cases hu : (FixedWidthCodec.optionFin symbols).decode (u.take (symbols + 1)) <;>
        cases hv : (FixedWidthCodec.optionFin symbols).decode (v.take (symbols + 1)) <;>
        cases ht : ((FixedWidthCodec.optionFin symbols).vector count).decode (u.drop (symbols + 1)) <;>
        cases hs : ((FixedWidthCodec.optionFin symbols).vector count).decode (v.drop (symbols + 1)) <;>
        simp [test, tail, FixedWidthCodec.vector, FixedWidthCodec.transport,
          FixedWidthCodec.prod, width, hu, hv, ht, hs, cellsTest, Bool.and_assoc]

/-- Once the head cell has been checked, all remaining cells must agree. -/
theorem cellsTest_after_head (observed : Cell symbols) (write : Option (Fin symbols))
    (count : ℕ) (a b : Fin count → Cell symbols) :
    cellsTest symbols observed write count 0 true a b = decide (a = b) := by
  induction count with
  | zero =>
      have same : a = b := Subsingleton.elim _ _
      simp [cellsTest, same]
  | succ count ih =>
      have same : a = b ↔ a 0 = b 0 ∧ Fin.tail a = Fin.tail b := by
        constructor
        · rintro rfl; exact ⟨rfl, rfl⟩
        · rintro ⟨h, t⟩
          rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, h, t]
      simp [cellsTest, ih, same, eq_comm]

/-- Before visiting the head, precisely that cell is checked against the
observed symbol and permitted write; every other cell is unchanged. -/
theorem cellsTest_at_head (observed : Cell symbols) (write : Option (Fin symbols))
    (count : ℕ) (head : Fin count) (a b : Fin count → Cell symbols) :
    cellsTest symbols observed write count head.val false a b =
      decide (a head = observed ∧ b = Function.update a head (written symbols write (a head))) := by
  induction count with
  | zero => exact Fin.elim0 head
  | succ count ih =>
      refine Fin.cases ?_ (fun head => ?_) head
      · have updated : b = Function.update a 0 (written symbols write (a 0)) ↔
            b 0 = written symbols write (a 0) ∧ Fin.tail a = Fin.tail b := by
          constructor
          · intro h
            subst b
            simp [Fin.tail, Function.update_apply]
          · rintro ⟨h, t⟩
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using h
            · have eq := congrFun t j
              simpa [Fin.tail] using eq.symm
        simp [cellsTest, cellsTest_after_head, updated, Bool.and_assoc, and_assoc]
      · have neq : (0 : Fin (count + 1)) ≠ head.succ := (Fin.succ_ne_zero head).symm
        have updated : b = Function.update a head.succ (written symbols write (a head.succ)) ↔
            a 0 = b 0 ∧ Fin.tail b = Function.update (Fin.tail a) head (written symbols write (a head.succ)) := by
          constructor
          · intro h
            subst b
            constructor
            · simp [Function.update_of_ne neq]
            · funext j; simp [Fin.tail, Function.update_apply]
          · rintro ⟨h, t⟩
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa [Function.update_of_ne neq] using h.symm
            · have eq := congrFun t j
              simpa [Fin.tail, Function.update_apply] using eq
        simp [cellsTest, ih, updated, Fin.tail, Bool.and_assoc, Bool.and_left_comm, eq_comm]

/-- Exact work-window meaning: both inputs decode, the source observation
matches, and the target array is the permitted single-cell update. -/
theorem test_correct (observed : Cell symbols) (write : Option (Fin symbols))
    (count : ℕ) (head : Fin count) (u v : List Bool) :
    test symbols observed write count head.val false u v = true ↔
      ∃ a b : Fin count → Cell symbols,
        ((FixedWidthCodec.optionFin symbols).vector count).decode u = some a ∧
        ((FixedWidthCodec.optionFin symbols).vector count).decode v = some b ∧
        a head = observed ∧ b = Function.update a head (written symbols write (a head)) := by
  rw [test_eq_decoded]
  simp only [Option.any_eq_true, cellsTest_at_head, decide_eq_true_eq]
  aesop

/-- Native bounded trace for the exact decoded-array update predicate. The
space bound includes every intermediate stack configuration, also on rejection. -/
theorem run_correct (observed : Cell symbols) (write : Option (Fin symbols))
    (answer : Bool) (count : ℕ) (head : Fin count) (u v : List Bool) (r : ℕ)
    (hu : u.length ≤ r) (hv : v.length ≤ r) (hc : count ≤ r) :
    ∃ result stk,
      StackSpace.Trace (program symbols observed write) r
        (StackSpace.localConfig (.loop false) (carrying answer false) (registers u v count head.val))
        (StackSpace.localConfig .done (carrying answer result) stk) ∧
      (result = true ↔ ∃ a b : Fin count → Cell symbols,
        ((FixedWidthCodec.optionFin symbols).vector count).decode u = some a ∧
        ((FixedWidthCodec.optionFin symbols).vector count).decode v = some b ∧
        a head = observed ∧ b = Function.update a head (written symbols write (a head))) := by
  obtain ⟨stk, trace⟩ := run symbols observed write answer count head.val false u v r hu hv hc
    (head.isLt.le.trans hc)
  exact ⟨_, stk, trace, test_correct symbols observed write count head u v⟩

end ComplexityOfGenerators.Simulation.SavitchMachine.WorkWindow
