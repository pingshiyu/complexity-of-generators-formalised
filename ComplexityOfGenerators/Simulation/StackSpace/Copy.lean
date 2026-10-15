import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Copying a register while preserving its contents. One temporary stack is
emptied again before returning; the copying loops operate on individual cells. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def replaceThree (stk : Fin (k + 1) → List S) (a b c : Fin (k + 1))
    (x y z : List S) : Fin (k + 1) → List S :=
  Function.update (replaceTwo stk a b x y) c z

theorem replaceThree_a (stk : Fin (k + 1) → List S) (a b c : Fin (k + 1))
    (ab : a ≠ b) (ac : a ≠ c) (x y z : List S) : replaceThree stk a b c x y z a = x := by
  simp [replaceThree, replaceTwo, ab, ac]

theorem replaceThree_b (stk : Fin (k + 1) → List S) (a b c : Fin (k + 1))
    (bc : b ≠ c) (x y z : List S) : replaceThree stk a b c x y z b = y := by
  simp [replaceThree, replaceTwo, bc]

@[simp] theorem replaceThree_c (stk : Fin (k + 1) → List S) (a b c : Fin (k + 1))
    (x y z : List S) : replaceThree stk a b c x y z c = z := by
  simp [replaceThree]

theorem replaceThree_replace (stk : Fin (k + 1) → List S) (a b c : Fin (k + 1))
    (x y z x' y' z' : List S) :
    replaceThree (replaceThree stk a b c x y z) a b c x' y' z' = replaceThree stk a b c x' y' z' := by
  funext j
  by_cases hc : j = c <;> by_cases hb : j = b <;> by_cases ha : j = a <;>
    simp_all [replaceThree, replaceTwo]

theorem replaceThree_bound (stk : Fin (k + 1) → List S) (a b c : Fin (k + 1)) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) (x y z : List S)
    (hx : x.length ≤ r) (hy : y.length ≤ r) (hz : z.length ≤ r) :
    ∀ j, (replaceThree stk a b c x y z j).length ≤ r := by
  intro j
  by_cases hc : j = c
  · simpa [replaceThree, hc] using hz
  · simpa [replaceThree, hc] using replaceTwo_bound stk a b r bound x y hx hy j

def duplicateCode [Inhabited S] (src left right : Fin (k + 1)) (loop exit : Q) :
    Stmt S Q (V × Option S) k :=
  .pop src (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (.push left (fun v => v.2.getD default)
        (.push right (fun v => v.2.getD default)
          (.load (fun v => (v.1, none)) (.goto fun _ => loop))))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

variable [Inhabited S]
variable (P : Q → Stmt S Q (V × Option S) k)
variable (src left right : Fin (k + 1)) (sl : src ≠ left) (sr : src ≠ right) (lr : left ≠ right)
variable (loop exit : Q) (table : P loop = duplicateCode src left right loop exit)

include table sl sr lr

theorem duplicate_continue (v : V) (stk : Fin (k + 1) → List S) (s : S) (rest : List S)
    (head : stk src = s :: rest) :
    TM2.step P (localConfig loop v stk) = some (localConfig loop v
      (replaceThree stk src left right rest (s :: stk left) (s :: stk right))) := by
  simp [TM2.step, localConfig, table, duplicateCode, TM2.stepAux, head,
    replaceThree, replaceTwo, Function.update_of_ne (Ne.symm sl),
    Function.update_of_ne (Ne.symm sr), Function.update_of_ne (Ne.symm lr)]

omit sl sr lr in
theorem duplicate_empty (v : V) (stk : Fin (k + 1) → List S) (head : stk src = []) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v stk) := by
  have upd : Function.update stk src [] = stk := by
    rw [← head]; exact Function.update_eq_self src stk
  simp [TM2.step, localConfig, table, duplicateCode, TM2.stepAux, head, upd]

/-- Reverse one stack onto two destinations. The two growing destinations
are bounded separately, including any pre-existing suffixes. -/
theorem duplicate_all (v : V) (stk : Fin (k + 1) → List S)
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (leftRoom : (stk src).length + (stk left).length ≤ r)
    (rightRoom : (stk src).length + (stk right).length ≤ r) :
    Trace P r (localConfig loop v stk) (localConfig exit v
      (replaceThree stk src left right [] ((stk src).reverse ++ stk left) ((stk src).reverse ++ stk right))) := by
  generalize hs : stk src = word at *
  induction word generalizing stk with
  | nil =>
      have next := duplicate_empty P src left right loop exit table v stk hs
      have finish : replaceThree stk src left right [] ([] ++ stk left) ([] ++ stk right) = stk := by
        simp only [List.nil_append, replaceThree, replaceTwo]
        have upd : Function.update stk src [] = stk := by rw [← hs]; exact Function.update_eq_self _ _
        rw [upd, Function.update_eq_self, Function.update_eq_self]
      simpa only [List.reverse_nil, finish] using Trace.step
        (show Within r (localConfig loop v stk) from bound) next (.refl _ bound)
  | cons s word ih =>
      let nextStk := replaceThree stk src left right word (s :: stk left) (s :: stk right)
      have next := duplicate_continue P src left right sl sr lr loop exit table v stk s word hs
      have newBound : ∀ j, (nextStk j).length ≤ r := by
        apply replaceThree_bound stk src left right r bound
        · have h := bound src; rw [hs] at h; simp only [List.length_cons] at h; omega
        · simp only [List.length_cons] at leftRoom ⊢; omega
        · simp only [List.length_cons] at rightRoom ⊢; omega
      have tail := ih nextStk newBound (replaceThree_a stk src left right sl sr _ _ _)
        (by simp only [nextStk, replaceThree_b stk src left right lr, List.length_cons] at *; omega)
        (by simp only [nextStk, replaceThree_c, List.length_cons] at *; omega)
      have finish : replaceThree nextStk src left right [] (word.reverse ++ nextStk left)
          (word.reverse ++ nextStk right) =
          replaceThree stk src left right [] ((s :: word).reverse ++ stk left) ((s :: word).reverse ++ stk right) := by
        simp only [nextStk, replaceThree_b stk src left right lr, replaceThree_c,
          replaceThree_replace, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [finish] at tail
      exact .step bound next tail

omit table sl sr lr in
/-- Two concrete loops copy a stack without consuming it. Temporary storage
is empty both on entry and on return. -/
theorem copy_all (copyLoop : Q)
    (copyTable : P copyLoop = transferCode left src copyLoop loop (fun _ => true))
    (duplicateTable : P loop = duplicateCode src left right loop exit)
    (different₁ : src ≠ left) (different₂ : src ≠ right) (different₃ : left ≠ right)
    (v : V) (stk : Fin (k + 1) → List S) (scratch : stk src = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (room : (stk left).length + (stk right).length ≤ r) :
    Trace P r (localConfig copyLoop v stk)
      (localConfig exit v (Function.update stk right (stk left ++ stk right))) := by
  let middle := replaceTwo stk left src [] ((stk left).reverse ++ stk src)
  have first := transfer_all P left src different₁.symm copyLoop loop (fun _ => true) copyTable v stk
    (by simp) r bound (by simpa [scratch] using bound left)
  have middleBound := first.end_bound
  have tail := duplicate_all P src left right different₁ different₂ different₃ loop exit duplicateTable
    v middle r middleBound (by
      simp [middle, replaceTwo, scratch, different₁.symm]
      exact bound left) (by
      simpa [middle, replaceTwo, scratch, different₁, different₂.symm, different₃.symm] using room)
  have finish : replaceThree middle src left right [] ((middle src).reverse ++ middle left)
      ((middle src).reverse ++ middle right) = Function.update stk right (stk left ++ stk right) := by
    funext j
    by_cases hr : j = right
    · subst j
      simp [middle, replaceThree, replaceTwo, scratch, different₂.symm, different₃.symm]
    · by_cases hl : j = left
      · subst j
        simp [middle, replaceThree, replaceTwo, scratch, hr, different₁.symm]
      · by_cases hs : j = src
        · subst j
          simp [middle, replaceThree, replaceTwo, scratch, hr, hl]
        · simp [middle, replaceThree, replaceTwo, hr, hl, hs]
  rw [finish] at tail
  exact first.trans tail

omit table sl sr lr in
/-- Copy a register in reverse order while preserving the original. This is
the operation used to store a loaded frame and keep its fields for a child. -/
theorem copy_reverse (restoreLoop : Q)
    (duplicateTable : P loop = duplicateCode left src right loop restoreLoop)
    (restoreTable : P restoreLoop = transferCode src left restoreLoop exit (fun _ => true))
    (different₁ : src ≠ left) (different₂ : src ≠ right) (different₃ : left ≠ right)
    (v : V) (stk : Fin (k + 1) → List S) (scratch : stk src = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (room : (stk left).length + (stk right).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig exit v (Function.update stk right ((stk left).reverse ++ stk right))) := by
  let middle := replaceThree stk left src right [] ((stk left).reverse ++ stk src)
    ((stk left).reverse ++ stk right)
  have first := duplicate_all P left src right different₁.symm different₃ different₂
    loop restoreLoop duplicateTable v stk r bound (by simpa [scratch] using bound left) room
  have tail := transfer_all P src left different₁ restoreLoop exit (fun _ => true) restoreTable
    v middle (by simp) r first.end_bound (by
      simpa [middle, replaceThree, replaceTwo, scratch, different₁.symm, different₂, different₃] using bound left)
  have finish : replaceTwo middle src left [] ((middle src).reverse ++ middle left) =
      Function.update stk right ((stk left).reverse ++ stk right) := by
    funext j
    by_cases hr : j = right
    · subst j
      simp [middle, replaceThree, replaceTwo, scratch, different₂.symm, different₃.symm]
    · by_cases hl : j = left
      · subst j
        simp [middle, replaceThree, replaceTwo, scratch, hr, different₁.symm, different₂]
      · by_cases hs : j = src
        · subst j
          simp [middle, replaceThree, replaceTwo, scratch, hr, hl]
        · simp [middle, replaceThree, replaceTwo, hr, hl, hs]
  rw [finish] at tail
  exact first.trans tail

end ComplexityOfGenerators.Simulation.StackSpace
