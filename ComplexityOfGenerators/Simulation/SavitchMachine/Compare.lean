import ComplexityOfGenerators.Simulation.SavitchMachine.FieldCounter

/-! A destructive comparison of two scratch registers for configuration
checks. The equality result lives in finite control, and both registers are
empty at return. Every instruction reads at most one stack symbol. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Frames
set_option backward.isDefEq.respectTransparency false

variable {Q : Type} {k : ℕ}

def compareCode (left right : Fin (k + 1)) (loop exit : Q) : Stmt Symbol Q Local k :=
  .pop left (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (.pop right (fun v s =>
        ({v.1 with returned := some (v.1.returned.getD false && decide (v.2 = s))}, none))
        (.goto fun _ => loop))
      (.peek right (fun v s =>
        ({v.1 with returned := some (v.1.returned.getD false && s.isNone)}, none))
        (.goto fun _ => exit)))

variable (P : Q → Stmt Symbol Q Local k) (left right : Fin (k + 1)) (different : left ≠ right)
variable (loop exit : Q) (table : P loop = compareCode left right loop exit)
include table different

theorem compare_cons (answer carry : Bool) (stk : Fin (k + 1) → List Symbol)
    (bit : Symbol) (word : List Symbol) (head : stk left = bit :: word) :
    TM2.step P (localConfig loop (carrying answer carry) stk) =
      some (localConfig loop (carrying answer (carry && decide (some bit = (stk right).head?)))
        (replaceTwo stk left right word (stk right).tail)) := by
  simp [TM2.step, localConfig, table, compareCode, TM2.stepAux, head, carrying,
    replaceTwo, different.symm]

omit different in
theorem compare_nil (answer carry : Bool) (stk : Fin (k + 1) → List Symbol)
    (head : stk left = []) :
    TM2.step P (localConfig loop (carrying answer carry) stk) =
      some (localConfig exit (carrying answer (carry && decide (stk right = []))) stk) := by
  have unchanged : Function.update stk left [] = stk := by
    rw [← head]; exact Function.update_eq_self _ _
  cases last : stk right <;>
    simp [TM2.step, localConfig, table, compareCode, TM2.stepAux, head, carrying,
      unchanged, last]

/-- The comparison consumes the left register and the corresponding prefix
of the right register. A final emptiness test detects any remaining suffix. -/
theorem compare_scan (answer carry : Bool) (stk : Fin (k + 1) → List Symbol)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig loop (carrying answer carry) stk)
      (localConfig exit (carrying answer (carry && decide (stk left = stk right)))
        (replaceTwo stk left right [] ((stk right).drop (stk left).length))) := by
  generalize hl : stk left = l at *
  induction l generalizing stk carry with
  | nil =>
      have next := compare_nil P left right loop exit table answer carry stk hl
      have finish : replaceTwo stk left right [] (stk right) = stk := by
        rw [← hl]; exact replaceTwo_same stk left right
      simpa only [List.length_nil, List.drop_zero, finish, eq_comm (a := ([] : List Symbol))] using
        Trace.step (show Within r (localConfig loop (carrying answer carry) stk) from bound)
          next (.refl _ bound)
  | cons bit word ih =>
      let middle := replaceTwo stk left right word (stk right).tail
      have next := compare_cons P left right different loop exit table answer carry stk bit word hl
      have midBound : ∀ j, (middle j).length ≤ r := by
        apply replaceTwo_bound _ _ _ r bound
        · have h := bound left; rw [hl] at h; simp only [List.length_cons] at h; omega
        · have h := bound right; simp only [List.length_tail]; omega
      have tail := ih (carry && decide (some bit = (stk right).head?)) middle midBound
        (replaceTwo_get_src stk left right different _ _)
      have finish : replaceTwo middle left right [] ((middle right).drop word.length) =
          replaceTwo stk left right [] ((stk right).drop (bit :: word).length) := by
        simp only [middle, replaceTwo_get_dst, replaceTwo_replace _ _ _ different,
          List.drop_tail, List.length_cons]
      rw [finish] at tail
      have flag : (carry && decide (some bit = (stk right).head?) && decide (word = middle right)) =
          (carry && decide (bit :: word = stk right)) := by
        cases h : stk right <;>
          simp [middle, replaceTwo_get_dst, h, Bool.and_assoc, List.cons.injEq]
      rw [flag] at tail
      exact .step bound next tail

omit table in
/-- Compare two registers and clear both, preserving every other stack. -/
theorem compare_trace (clear : Q)
    (compareTable : P loop = compareCode left right loop clear)
    (clearTable : P clear = clearCode right clear exit (fun _ => true))
    (answer : Bool) (stk : Fin (k + 1) → List Symbol) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig loop (carrying answer true) stk)
      (localConfig exit (carrying answer (decide (stk left = stk right)))
        (replaceTwo stk left right [] [])) := by
  have first := compare_scan P left right different loop clear compareTable answer true stk r bound
  let middle := replaceTwo stk left right [] ((stk right).drop (stk left).length)
  have last := clear_all P right clear exit (fun _ => true) clearTable
    (carrying answer (decide (stk left = stk right))) middle (by simp) r first.end_bound
  have finish : Function.update middle right [] = replaceTwo stk left right [] [] := by
    simp [middle, replaceTwo, Function.update_idem]
  rw [finish] at last
  simpa only [Bool.true_and] using first.trans last

end ComplexityOfGenerators.Simulation.SavitchMachine
