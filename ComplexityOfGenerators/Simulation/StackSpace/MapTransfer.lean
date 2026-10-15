import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! A finite symbol map during a stack transfer. In particular, replacing
bits by zero builds the initial midpoint without storing a width in control. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

def mapTransferCode (source target : Fin (k + 1)) (loop exit : Q) (map : S → S) :
    Stmt S Q (V × Option S) k :=
  .pop source (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (.push target (fun v => map (v.2.getD default))
        (.load (fun v => (v.1, none)) (.goto fun _ => loop)))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

variable (P : Q → Stmt S Q (V × Option S) k)
variable (source target : Fin (k + 1)) (different : source ≠ target)
variable (loop exit : Q) (map : S → S)
variable (table : P loop = mapTransferCode source target loop exit map)
include table

theorem mapTransfer_empty (v : V) (stk : Fin (k + 1) → List S) (head : stk source = []) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v stk) := by
  have upd : Function.update stk source [] = stk := by
    rw [← head]; exact Function.update_eq_self source stk
  simp [TM2.step, localConfig, table, mapTransferCode, TM2.stepAux, head, upd]

include different

theorem mapTransfer_cons (v : V) (stk : Fin (k + 1) → List S) (bit : S) (rest : List S)
    (head : stk source = bit :: rest) :
    TM2.step P (localConfig loop v stk) = some (localConfig loop v
      (replaceTwo stk source target rest (map bit :: stk target))) := by
  simp [TM2.step, localConfig, table, mapTransferCode, TM2.stepAux, head,
    replaceTwo, different.symm]

theorem mapTransfer_all (v : V) (stk : Fin (k + 1) → List S) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) (room : (stk source).length + (stk target).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig exit v (replaceTwo stk source target [] ((stk source).reverse.map map ++ stk target))) := by
  generalize head : stk source = word at *
  induction word generalizing stk with
  | nil =>
      have next := mapTransfer_empty P source target loop exit map table v stk head
      have finish : replaceTwo stk source target [] (stk target) = stk := by
        rw [← head]; exact replaceTwo_same stk source target
      simpa only [List.reverse_nil, List.map_nil, List.nil_append, finish] using
        Trace.step (show Within r (localConfig loop v stk) from bound) next (.refl _ bound)
  | cons bit word ih =>
      let middle := replaceTwo stk source target word (map bit :: stk target)
      have next := mapTransfer_cons P source target different loop exit map table v stk bit word head
      have midBound : ∀ j, (middle j).length ≤ r := by
        apply replaceTwo_bound stk source target r bound
        · have h := bound source; rw [head] at h; simp only [List.length_cons] at h; omega
        · simp only [List.length_cons] at room ⊢; omega
      have tail := ih middle midBound (replaceTwo_get_src stk source target different _ _) (by
        simp only [middle, replaceTwo_get_dst, List.length_cons] at *; omega)
      have finish : replaceTwo middle source target [] (word.reverse.map map ++ middle target) =
          replaceTwo stk source target [] ((bit :: word).reverse.map map ++ stk target) := by
        simp only [middle, replaceTwo_get_dst, replaceTwo_replace _ _ _ different,
          List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append]
      rw [finish] at tail
      exact .step bound next tail

omit table in
/-- Push a delimited, possibly transformed field from a reversed register.
The temporary register is consumed, and the pre-existing target is preserved. -/
theorem push_field (entry : Q) (delimiter : S)
    (markTable : P entry = .push target (fun _ => delimiter) (.goto fun _ => loop))
    (copyTable : P loop = mapTransferCode source target loop exit map)
    (v : V) (stk : Fin (k + 1) → List S) (word : List S)
    (head : stk source = word.reverse) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : word.length + 1 + (stk target).length ≤ r) :
    Trace P r (localConfig entry v stk)
      (localConfig exit v (replaceTwo stk source target [] (word.map map ++ delimiter :: stk target))) := by
  let marked := Function.update stk target (delimiter :: stk target)
  have markedBound : ∀ j, (marked j).length ≤ r := by
    intro j
    by_cases h : j = target
    · subst j; simp only [marked, Function.update_self, List.length_cons]; omega
    · simpa only [marked, Function.update_of_ne h] using bound j
  have next : TM2.step P (localConfig entry v stk) = some (localConfig loop v marked) := by
    simp [TM2.step, localConfig, markTable, TM2.stepAux, marked]
  have last := mapTransfer_all P source target different loop exit map copyTable v marked r markedBound (by
    simp only [marked, Function.update_of_ne different, Function.update_self, head,
      List.length_reverse, List.length_cons]; omega)
  have finish : replaceTwo marked source target [] ((marked source).reverse.map map ++ marked target) =
      replaceTwo stk source target [] (word.map map ++ delimiter :: stk target) := by
    simp only [marked, Function.update_of_ne different, Function.update_self, head, List.reverse_reverse]
    funext j
    by_cases ht : j = target <;> by_cases hs : j = source <;> simp [replaceTwo, ht, hs, different]
  rw [finish] at last
  exact .step bound next last

end ComplexityOfGenerators.Simulation.StackSpace
