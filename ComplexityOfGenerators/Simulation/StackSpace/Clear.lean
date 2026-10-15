import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Erasing an entire temporary register, or only a delimited field, by
individual pop instructions. Erasure never increases any stack length. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def clearCode (src : Fin (k + 1)) (loop exit : Q) (keep : S → Bool) :
    Stmt S Q (V × Option S) k :=
  .pop src (fun v s => (v.1, s))
    (.branch (fun v => v.2.any keep)
      (.load (fun v => (v.1, none)) (.goto fun _ => loop))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

variable (P : Q → Stmt S Q (V × Option S) k) (src : Fin (k + 1))
variable (loop exit : Q) (keep : S → Bool) (table : P loop = clearCode src loop exit keep)
include table

theorem clear_continue (v : V) (stk : Fin (k + 1) → List S) (s : S) (rest : List S)
    (head : stk src = s :: rest) (more : keep s = true) :
    TM2.step P (localConfig loop v stk) = some (localConfig loop v (Function.update stk src rest)) := by
  simp [TM2.step, localConfig, table, clearCode, TM2.stepAux, head, more]

theorem clear_stop (v : V) (stk : Fin (k + 1) → List S) (s : S) (rest : List S)
    (head : stk src = s :: rest) (stop : keep s = false) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v (Function.update stk src rest)) := by
  simp [TM2.step, localConfig, table, clearCode, TM2.stepAux, head, stop]

theorem clear_empty (v : V) (stk : Fin (k + 1) → List S) (head : stk src = []) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v stk) := by
  have upd : Function.update stk src [] = stk := by rw [← head]; exact Function.update_eq_self _ _
  simp [TM2.step, localConfig, table, clearCode, TM2.stepAux, head, upd]

/-- Only the first field and its delimiter are erased; the suffix is intact. -/
theorem clear_field (v : V) (stk : Fin (k + 1) → List S) (field : List S) (delimiter : S) (suffix : List S)
    (head : stk src = field ++ delimiter :: suffix)
    (more : ∀ s ∈ field, keep s = true) (stop : keep delimiter = false)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig loop v stk) (localConfig exit v (Function.update stk src suffix)) := by
  induction field generalizing stk with
  | nil =>
      have h : stk src = delimiter :: suffix := by simpa using head
      have next := clear_stop P src loop exit keep table v stk delimiter suffix h stop
      have finalBound : ∀ j, (Function.update stk src suffix j).length ≤ r := by
        intro j
        by_cases same : j = src
        · have b := bound src; rw [h] at b; simp only [List.length_cons] at b
          simp [same]; omega
        · simpa [same] using bound j
      exact .step bound next (.refl _ finalBound)
  | cons s field ih =>
      let nextStk := Function.update stk src (field ++ delimiter :: suffix)
      have next := clear_continue P src loop exit keep table v stk s _ head (more s (by simp))
      have nextBound : ∀ j, (nextStk j).length ≤ r := by
        intro j
        by_cases same : j = src
        · have b := bound src; rw [head] at b
          simp only [List.cons_append, List.length_cons] at b
          simp only [nextStk, same, Function.update_self]; omega
        · simpa [nextStk, same] using bound j
      have tail := ih nextStk (by simp [nextStk]) (fun a h => more a (by simp [h])) nextBound
      have path := Trace.step (show Within r (localConfig loop v stk) from bound) next tail
      simpa only [nextStk, Function.update_idem] using path

theorem clear_all (v : V) (stk : Fin (k + 1) → List S) (more : ∀ s ∈ stk src, keep s = true)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig loop v stk) (localConfig exit v (Function.update stk src [])) := by
  generalize head : stk src = word at *
  induction word generalizing stk with
  | nil =>
      have next := clear_empty P src loop exit keep table v stk head
      have upd : Function.update stk src [] = stk := by rw [← head]; exact Function.update_eq_self _ _
      rw [upd]
      exact .step bound next (.refl _ bound)
  | cons s word ih =>
      let nextStk := Function.update stk src word
      have next := clear_continue P src loop exit keep table v stk s word head (more s (by simp))
      have nextBound : ∀ j, (nextStk j).length ≤ r := by
        intro j
        by_cases same : j = src
        · have b := bound src; rw [head] at b; simp only [List.length_cons] at b
          simp only [nextStk, same, Function.update_self]; omega
        · simpa [nextStk, same] using bound j
      have tail := ih nextStk nextBound (by simp [nextStk]) (fun a h => more a (by simp [h]))
      have path := Trace.step (show Within r (localConfig loop v stk) from bound) next tail
      simpa only [nextStk, Function.update_idem] using path

end ComplexityOfGenerators.Simulation.StackSpace
