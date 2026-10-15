import ComplexityOfGenerators.Simulation.StackSpace.Constants
import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Multiply a unary register by a fixed program constant. Each source cell
causes a fixed, finite sequence of pushes. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def expandCode (source destination : Fin (k + 1)) (symbol : S) (count : ℕ)
    (loop exit : Q) : Stmt S Q (V × Option S) k :=
  .pop source (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (pushCopies destination symbol count (.load (fun v => (v.1, none)) (.goto fun _ => loop)))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

variable (P : Q → Stmt S Q (V × Option S) k) (source destination : Fin (k + 1))
variable (different : source ≠ destination) (symbol : S) (count : ℕ) (loop exit : Q)
variable (table : P loop = expandCode source destination symbol count loop exit)

include table in
theorem expand_empty (v : V) (stk : Fin (k + 1) → List S) (empty : stk source = []) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v stk) := by
  have unchanged : Function.update stk source [] = stk := by
    rw [← empty]; exact Function.update_eq_self _ _
  simp [TM2.step, localConfig, table, expandCode, TM2.stepAux, empty, unchanged]

include table different in
theorem expand_cons (v : V) (stk : Fin (k + 1) → List S) (a : S) (rest : List S)
    (head : stk source = a :: rest) :
    TM2.step P (localConfig loop v stk) = some (localConfig loop v
      (replaceTwo stk source destination rest (List.replicate count symbol ++ stk destination))) := by
  simp [TM2.step, localConfig, table, expandCode, TM2.stepAux, head,
    pushCopies_stepAux, replaceTwo, different.symm]

include table different in
/-- A uniform loop with a fixed expansion factor, with all intermediate
source configurations bounded. The native compiler separately charges the
fixed number of pushes inside an instruction. -/
theorem expand_all (v : V) (stk : Fin (k + 1) → List S) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r)
    (room : count * (stk source).length + (stk destination).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig exit v (replaceTwo stk source destination []
        (List.replicate (count * (stk source).length) symbol ++ stk destination))) := by
  generalize head : stk source = word at *
  induction word generalizing stk with
  | nil =>
      have finish : replaceTwo stk source destination [] (stk destination) = stk := by
        rw [← head]; exact replaceTwo_same stk source destination
      simpa [finish] using Trace.step
        (show Within r (localConfig loop v stk) from bound)
        (expand_empty P source destination symbol count loop exit table v stk head) (.refl _ bound)
  | cons a word ih =>
      let middle := replaceTwo stk source destination word
        (List.replicate count symbol ++ stk destination)
      have midBound : ∀ j, (middle j).length ≤ r := by
        apply replaceTwo_bound stk source destination r bound
        · have h := bound source; rw [head] at h; simp only [List.length_cons] at h; omega
        · simp only [List.length_append, List.length_replicate]
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at room
          omega
      have tail := ih middle midBound (replaceTwo_get_src stk source destination different _ _) (by
        simpa only [middle, replaceTwo_get_dst, List.length_append, List.length_replicate,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (show count * word.length + count + (stk destination).length ≤ r by
            simpa only [List.length_cons, Nat.mul_add, Nat.mul_one] using room))
      have finish : replaceTwo middle source destination []
          (List.replicate (count * word.length) symbol ++ middle destination) =
          replaceTwo stk source destination []
            (List.replicate (count * (a :: word).length) symbol ++ stk destination) := by
        simp only [middle, replaceTwo_get_dst, replaceTwo_replace _ _ _ different,
          List.length_cons, Nat.mul_add, Nat.mul_one, List.replicate_add, List.append_assoc]
      rw [finish] at tail
      exact .step bound (expand_cons P source destination different symbol count loop exit table v stk a word head) tail

end ComplexityOfGenerators.Simulation.StackSpace
