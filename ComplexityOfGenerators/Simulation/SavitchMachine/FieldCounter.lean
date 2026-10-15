import ComplexityOfGenerators.Simulation.SavitchMachine.ReturnTrue
import Complexitylib.Classes.Containments.Internal.SavitchBits

/-! Increment a delimited midpoint in place. The delimiter and suspended
frames are preserved. The carry occupies one bit of finite control; a temporary
stack holds the reversed result and is empty again on return. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

def carrying (answer carry : Bool) : Status := ⟨false, answer, some carry⟩

variable {k : ℕ}

def fieldCounterCode {Q : Type} (source scratch : Fin (k + 1)) (scan restore : Q) :
    Stmt Symbol Q Local k :=
  .peek source (fun v s => (v.1, s))
    (.branch (fun v => v.2.join.isSome)
      (.pop source (fun v _ => v)
        (.push scratch (fun v => some (xor (v.1.returned.getD false) (v.2.join.getD false)))
          (.load (fun v => ({v.1 with returned := some (v.1.returned.getD false && v.2.join.getD false)}, none))
            (.goto fun _ => scan))))
      (.load (fun v => (v.1, none)) (.goto fun _ => restore)))

variable {Q : Type} (P : Q → Stmt Symbol Q Local k)
variable (source scratch : Fin (k + 1)) (different : source ≠ scratch) (scan restore exit : Q)
variable (scanTable : P scan = fieldCounterCode source scratch scan restore)
include scanTable

theorem fieldCounter_stop (answer carry : Bool) (stk : Fin (k + 1) → List Symbol) (suffix : List Symbol)
    (head : stk source = none :: suffix) :
    TM2.step P (localConfig scan (carrying answer carry) stk) =
      some (localConfig restore (carrying answer carry) stk) := by
  simp [TM2.step, localConfig, scanTable, fieldCounterCode, TM2.stepAux, head]

include different in
theorem fieldCounter_bit (answer carry bit : Bool) (stk : Fin (k + 1) → List Symbol) (rest : List Symbol)
    (head : stk source = some bit :: rest) :
    TM2.step P (localConfig scan (carrying answer carry) stk) =
      some (localConfig scan (carrying answer (carry && bit))
        (replaceTwo stk source scratch rest (some (xor carry bit) :: stk scratch))) := by
  simp [TM2.step, localConfig, scanTable, fieldCounterCode, TM2.stepAux, head,
    carrying, replaceTwo, Function.update_of_ne different.symm]

include different in
/-- During the scan, source and scratch jointly contain exactly the original
number of bits. The source's untouched suffix is charged as well. -/
theorem fieldCounter_scan (answer carry : Bool) (stk : Fin (k + 1) → List Symbol) (word : List Bool)
    (suffix : List Symbol) (head : stk source = word.map some ++ none :: suffix)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : word.length + (stk scratch).length ≤ r) :
    Trace P r (localConfig scan (carrying answer carry) stk)
      (localConfig restore (carrying answer (addBit carry word).1)
        (replaceTwo stk source scratch (none :: suffix)
          ((addBit carry word).2.reverse.map some ++ stk scratch))) := by
  induction word generalizing carry stk with
  | nil =>
      have next := fieldCounter_stop P source scratch scan restore scanTable answer carry stk suffix head
      have unchanged : replaceTwo stk source scratch (none :: suffix) (stk scratch) = stk := by
        simp only [List.map_nil, List.nil_append] at head
        rw [← head]; exact replaceTwo_same stk source scratch
      simpa only [addBit, List.reverse_nil, List.map_nil, List.nil_append, unchanged] using
        Trace.step (show Within r (localConfig scan (carrying answer carry) stk) from bound)
          next (.refl _ bound)
  | cons bit word ih =>
      let middle := replaceTwo stk source scratch (word.map some ++ none :: suffix)
        (some (xor carry bit) :: stk scratch)
      have next := fieldCounter_bit P source scratch different scan restore scanTable
        answer carry bit stk _ head
      have midBound : ∀ j, (middle j).length ≤ r := by
        apply replaceTwo_bound stk source scratch r bound
        · have h := bound source
          simp only [head, List.map_cons, List.cons_append, List.length_cons] at h
          omega
        · simp only [List.length_cons] at room ⊢; omega
      have tail := ih (carry && bit) middle
        (replaceTwo_get_src stk source scratch different _ _) midBound (by
          simp only [middle, replaceTwo_get_dst, List.length_cons] at *; omega)
      have finish : replaceTwo middle source scratch (none :: suffix)
          ((addBit (carry && bit) word).2.reverse.map some ++ middle scratch) =
          replaceTwo stk source scratch (none :: suffix)
            ((addBit carry (bit :: word)).2.reverse.map some ++ stk scratch) := by
        simp only [middle, replaceTwo_get_dst, replaceTwo_replace _ _ _ different,
          addBit, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append]
      rw [finish] at tail
      exact .step bound next tail

include different
omit scanTable in
/-- The complete counter routine implements the library's increment and
returns its overflow flag, preserving every other frame field. -/
theorem fieldCounter_trace
    (scanTable : P scan = fieldCounterCode source scratch scan restore)
    (restoreTable : P restore = transferCode scratch source restore exit (fun _ => true))
    (answer carry : Bool) (stk : Fin (k + 1) → List Symbol) (word : List Bool) (suffix : List Symbol)
    (head : stk source = word.map some ++ none :: suffix) (empty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig scan (carrying answer carry) stk)
      (localConfig exit (carrying answer (addBit carry word).1)
        (Function.update stk source ((addBit carry word).2.map some ++ none :: suffix))) := by
  have room : word.length ≤ r := by
    have h := bound source
    simp only [head, List.length_append, List.length_map, List.length_cons] at h
    omega
  have first := fieldCounter_scan P source scratch different scan restore scanTable
    answer carry stk word suffix head r bound (by simpa [empty] using room)
  let middle := replaceTwo stk source scratch (none :: suffix)
    ((addBit carry word).2.reverse.map some ++ stk scratch)
  have last := transfer_all P scratch source different.symm restore exit (fun _ => true)
    restoreTable (carrying answer (addBit carry word).1) middle (by simp) r first.end_bound (by
      have h := bound source
      simp only [head, List.length_append, List.length_map, List.length_cons] at h
      simpa only [middle, replaceTwo_get_src _ _ _ different, replaceTwo_get_dst, empty,
        List.append_nil, List.length_map, List.length_reverse, addBit_length, List.length_cons] using h)
  have finish : replaceTwo middle scratch source [] ((middle scratch).reverse ++ middle source) =
      Function.update stk source ((addBit carry word).2.map some ++ none :: suffix) := by
    funext j
    by_cases hs : j = source
    · subst j
      simp [middle, replaceTwo, different, empty, ← List.map_reverse]
    · by_cases ht : j = scratch
      · subst j
        simp [middle, replaceTwo, hs, empty]
      · simp [middle, replaceTwo, hs, ht]
  rw [finish] at last
  exact first.trans last

end ComplexityOfGenerators.Simulation.SavitchMachine
