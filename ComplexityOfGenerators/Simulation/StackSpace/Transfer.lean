import ComplexityOfGenerators.Simulation.StackSpace.Trace

/-!
# Delimited field transfer in finite stack programs

The routine reads and removes one symbol at a time. It reverses a field onto
another stack and consumes its delimiter. It preserves all other stacks and
the caller's finite local state. Program-table equalities allow the routine to
be embedded at any pair of labels of a larger finite program.
-/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def transferCode [Inhabited S] (src dst : Fin (k + 1)) (loop exit : Q) (keep : S → Bool) :
    Stmt S Q (V × Option S) k :=
  .pop src (fun v s => (v.1, s))
    (.branch (fun v => v.2.any keep)
      (.push dst (fun v => v.2.getD default)
        (.load (fun v => (v.1, none)) (.goto fun _ => loop)))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

def localConfig (q : Q) (v : V) (stk : Fin (k + 1) → List S) : Source S Q (V × Option S) k :=
  ⟨some q, (v, none), stk⟩

def replaceTwo (stk : Fin (k + 1) → List S) (src dst : Fin (k + 1)) (left right : List S) :=
  Function.update (Function.update stk src left) dst right

theorem replaceTwo_same (stk : Fin (k + 1) → List S) (src dst : Fin (k + 1)) :
    replaceTwo stk src dst (stk src) (stk dst) = stk := by
  simp [replaceTwo, Function.update_eq_self]

theorem replaceTwo_get_src (stk : Fin (k + 1) → List S) (src dst : Fin (k + 1))
    (different : src ≠ dst) (left right : List S) :
    replaceTwo stk src dst left right src = left := by
  simp [replaceTwo, different]

theorem replaceTwo_get_dst (stk : Fin (k + 1) → List S) (src dst : Fin (k + 1))
    (left right : List S) : replaceTwo stk src dst left right dst = right := by
  simp [replaceTwo]

theorem replaceTwo_replace (stk : Fin (k + 1) → List S) (src dst : Fin (k + 1))
    (different : src ≠ dst) (a b c d : List S) :
    replaceTwo (replaceTwo stk src dst a b) src dst c d = replaceTwo stk src dst c d := by
  funext j
  by_cases hs : j = src <;> by_cases hd : j = dst <;>
    simp_all [replaceTwo]

theorem replaceTwo_bound (stk : Fin (k + 1) → List S) (src dst : Fin (k + 1))
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (left right : List S)
    (hl : left.length ≤ r) (hr : right.length ≤ r) :
    ∀ j, (replaceTwo stk src dst left right j).length ≤ r := by
  intro j
  by_cases hd : j = dst
  · simpa [replaceTwo, hd] using hr
  · by_cases hs : j = src
    · subst j; simpa [replaceTwo, hd] using hl
    · simpa [replaceTwo, hd, hs] using bound j

variable [Inhabited S]

variable (P : Q → Stmt S Q (V × Option S) k)
variable (src dst : Fin (k + 1)) (different : src ≠ dst) (loop exit : Q) (keep : S → Bool)
variable (table : P loop = transferCode src dst loop exit keep)

include table different

theorem transfer_continue (v : V) (stk : Fin (k + 1) → List S)
    (s : S) (rest : List S) (head : stk src = s :: rest) (more : keep s = true) :
    TM2.step P (localConfig loop v stk) =
      some (localConfig loop v (replaceTwo stk src dst rest (s :: stk dst))) := by
  simp [TM2.step, localConfig, table, transferCode, TM2.stepAux, head, more,
    replaceTwo, Function.update_of_ne (Ne.symm different)]

omit different in
theorem transfer_stop (v : V) (stk : Fin (k + 1) → List S)
    (s : S) (rest : List S) (head : stk src = s :: rest) (stop : keep s = false) :
    TM2.step P (localConfig loop v stk) =
      some (localConfig exit v (Function.update stk src rest)) := by
  simp [TM2.step, localConfig, table, transferCode, TM2.stepAux, head, stop]

omit different in
theorem transfer_empty (v : V) (stk : Fin (k + 1) → List S) (head : stk src = []) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v stk) := by
  have upd : Function.update stk src [] = stk := by
    rw [← head]; exact Function.update_eq_self src stk
  simp [TM2.step, localConfig, table, transferCode, TM2.stepAux, head, upd]

/-- Transfer a delimited field without touching the suffix below its delimiter.
The bound charges the growing destination and every untouched stack. -/
theorem transfer_field (v : V) (stk : Fin (k + 1) → List S)
    (field : List S) (delimiter : S) (suffix : List S)
    (head : stk src = field ++ delimiter :: suffix)
    (more : ∀ s ∈ field, keep s = true) (stop : keep delimiter = false)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (room : field.length + (stk dst).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig exit v (replaceTwo stk src dst suffix (field.reverse ++ stk dst))) := by
  induction field generalizing stk with
  | nil =>
      have hs : stk src = delimiter :: suffix := by simpa using head
      have next := transfer_stop P src dst loop exit keep table v stk delimiter suffix hs stop
      have bound' : ∀ j, (Function.update stk src suffix j).length ≤ r := by
        intro j
        by_cases h : j = src
        · have hsrc := bound src; simp [hs] at hsrc; simp [h]; omega
        · simpa [h] using bound j
      have finish : replaceTwo stk src dst suffix ([] ++ stk dst) = Function.update stk src suffix := by
        simp [replaceTwo, Function.update_of_ne (Ne.symm different)]
      simpa only [List.reverse_nil, finish] using Trace.step
        (show Within r (localConfig loop v stk) from bound) next (.refl _ bound')
  | cons s field ih =>
      let nextStk := replaceTwo stk src dst (field ++ delimiter :: suffix) (s :: stk dst)
      have hs : stk src = s :: (field ++ delimiter :: suffix) := head
      have next := transfer_continue P src dst different loop exit keep table v stk s _ hs (more s (by simp))
      have newBound : ∀ j, (nextStk j).length ≤ r := by
        apply replaceTwo_bound _ _ _ r bound
        · have hsrc := bound src; simp [hs] at hsrc; simpa using Nat.le_of_succ_le hsrc
        · simp only [List.length_cons] at room ⊢; omega
      have tail := ih nextStk (replaceTwo_get_src stk src dst different _ _)
        (fun a h => more a (by simp [h])) newBound (by
          simp only [nextStk, replaceTwo_get_dst, List.length_cons] at *
          omega)
      have finish : replaceTwo nextStk src dst suffix (field.reverse ++ nextStk dst) =
          replaceTwo stk src dst suffix ((s :: field).reverse ++ stk dst) := by
        simp only [nextStk, replaceTwo_get_dst, replaceTwo_replace stk src dst different,
          List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [finish] at tail
      exact .step bound next tail

/-- The same loop transfers an entire stack when every symbol is retained. -/
theorem transfer_all (v : V) (stk : Fin (k + 1) → List S)
    (more : ∀ s ∈ stk src, keep s = true)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (room : (stk src).length + (stk dst).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig exit v (replaceTwo stk src dst [] ((stk src).reverse ++ stk dst))) := by
  generalize hs : stk src = field at *
  induction field generalizing stk with
  | nil =>
      have next := transfer_empty P src dst loop exit keep table v stk hs
      have finish : replaceTwo stk src dst [] ([] ++ stk dst) = stk := by
        have h := replaceTwo_same stk src dst
        rw [hs] at h
        simpa using h
      simpa only [List.reverse_nil, finish] using Trace.step
        (show Within r (localConfig loop v stk) from bound) next (.refl _ bound)
  | cons s field ih =>
      let nextStk := replaceTwo stk src dst field (s :: stk dst)
      have next := transfer_continue P src dst different loop exit keep table v stk s field hs (more s (by simp))
      have newBound : ∀ j, (nextStk j).length ≤ r := by
        apply replaceTwo_bound _ _ _ r bound
        · have h := bound src; rw [hs] at h; simp only [List.length_cons] at h; omega
        · simp only [List.length_cons] at room ⊢; omega
      have tail := ih nextStk newBound (replaceTwo_get_src stk src dst different _ _)
        (fun a h => more a (by simp [h]))
        (by simp only [nextStk, replaceTwo_get_dst, List.length_cons] at *; omega)
      have finish : replaceTwo nextStk src dst [] (field.reverse ++ nextStk dst) =
          replaceTwo stk src dst [] ((s :: field).reverse ++ stk dst) := by
        simp only [nextStk, replaceTwo_get_dst, replaceTwo_replace stk src dst different,
          List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [finish] at tail
      exact .step bound next tail

end ComplexityOfGenerators.Simulation.StackSpace
