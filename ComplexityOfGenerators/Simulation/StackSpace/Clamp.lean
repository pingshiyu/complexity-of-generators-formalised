import ComplexityOfGenerators.Simulation.StackSpace.Copy
import ComplexityOfGenerators.Simulation.StackSpace.Clear

/-! A bounded transfer, controlled by a unary supply stack. The supply is
restored before return. This is used when decoding configuration coordinates:
clamping after each binary digit prevents malformed coordinates from allocating
an exponentially large unary value. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

def replaceFour (stk : Fin (k + 1) → List S) (a b c d : Fin (k + 1))
    (w x y z : List S) : Fin (k + 1) → List S :=
  Function.update (replaceThree stk a b c w x y) d z

def clampCode (source supply destination scratch : Fin (k + 1)) (loop exit : Q) :
    Stmt S Q (V × Option S) k :=
  .peek source (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (.peek supply (fun v s => (v.1, s))
        (.branch (fun v => v.2.isSome)
          (.pop source (fun v s => (v.1, s))
            (.push destination (fun v => v.2.getD default)
              (.pop supply (fun v s => (v.1, s))
                (.push scratch (fun v => v.2.getD default)
                  (.load (fun v => (v.1, none)) (.goto fun _ => loop))))))
          (.load (fun v => (v.1, none)) (.goto fun _ => exit))))
      (.load (fun v => (v.1, none)) (.goto fun _ => exit)))

variable (P : Q → Stmt S Q (V × Option S) k)
variable (slots : Fin 4 ↪ Fin (k + 1)) (loop exit : Q)
variable (table : P loop = clampCode (slots 0) (slots 1) (slots 2) (slots 3) loop exit)

private theorem slots_ne {a b : Fin 4} (h : a ≠ b) : slots a ≠ slots b :=
  fun same => h (slots.injective same)

include table in
theorem clamp_stop (v : V) (stk : Fin (k + 1) → List S)
    (empty : stk (slots 0) = [] ∨ stk (slots 1) = []) :
    TM2.step P (localConfig loop v stk) = some (localConfig exit v stk) := by
  rcases empty with empty | empty
  · simp [TM2.step, localConfig, table, clampCode, TM2.stepAux, empty]
  · cases source : stk (slots 0) <;>
      simp [TM2.step, localConfig, table, clampCode, TM2.stepAux, empty, source]

include table in
theorem clamp_cons (v : V) (stk : Fin (k + 1) → List S) (a b : S) (as bs : List S)
    (source : stk (slots 0) = a :: as) (supply : stk (slots 1) = b :: bs) :
    TM2.step P (localConfig loop v stk) = some (localConfig loop v
      (replaceFour stk (slots 0) (slots 1) (slots 2) (slots 3)
        as bs (a :: stk (slots 2)) (b :: stk (slots 3)))) := by
  simp only [TM2.step, localConfig, table, clampCode, TM2.stepAux, source, supply]
  simp [replaceFour, replaceThree, replaceTwo, Function.update_apply,
    slots_ne slots, show (0 : Fin 4) ≠ 1 by decide,
    show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) ≠ 2 by decide,
    show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide]
  funext j
  by_cases h₃ : j = slots 3 <;> by_cases h₂ : j = slots 2 <;>
    by_cases h₁ : j = slots 1 <;> by_cases h₀ : j = slots 0 <;>
    simp_all [Function.update_apply]

/-- Four-register updates preserve the bounds of all other registers. -/
theorem replaceFour_bound (stk : Fin (k + 1) → List S) (a b c d : Fin (k + 1))
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (w x y z : List S)
    (hw : w.length ≤ r) (hx : x.length ≤ r) (hy : y.length ≤ r) (hz : z.length ≤ r) :
    ∀ j, (replaceFour stk a b c d w x y z j).length ≤ r := by
  intro j
  by_cases h : j = d
  · simpa [replaceFour, h] using hz
  · simpa [replaceFour, h] using replaceThree_bound stk a b c r bound w x y hw hx hy j

theorem replaceFour_replace (stk : Fin (k + 1) → List S) (a b c d : Fin (k + 1))
    (w x y z w' x' y' z' : List S) :
    replaceFour (replaceFour stk a b c d w x y z) a b c d w' x' y' z' =
      replaceFour stk a b c d w' x' y' z' := by
  funext j
  by_cases hd : j = d <;> by_cases hc : j = c <;> by_cases hb : j = b <;> by_cases ha : j = a <;>
    simp_all [replaceFour, replaceThree, replaceTwo]

include table in
/-- Transfer precisely the common prefix length. Both growing stacks are
charged separately; the original source and supply can have different lengths. -/
theorem clamp_scan (v : V) (stk : Fin (k + 1) → List S) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r)
    (destRoom : min (stk (slots 0)).length (stk (slots 1)).length + (stk (slots 2)).length ≤ r)
    (scratchRoom : min (stk (slots 0)).length (stk (slots 1)).length + (stk (slots 3)).length ≤ r) :
    let count := min (stk (slots 0)).length (stk (slots 1)).length
    Trace P r (localConfig loop v stk)
      (localConfig exit v (replaceFour stk (slots 0) (slots 1) (slots 2) (slots 3)
        ((stk (slots 0)).drop count) ((stk (slots 1)).drop count)
        (((stk (slots 0)).take count).reverse ++ stk (slots 2))
        (((stk (slots 1)).take count).reverse ++ stk (slots 3)))) := by
  dsimp only
  generalize source : stk (slots 0) = word at *
  induction word generalizing stk with
  | nil =>
      have next := clamp_stop P slots loop exit table v stk (Or.inl source)
      have finish : replaceFour stk (slots 0) (slots 1) (slots 2) (slots 3)
          [] (stk (slots 1)) (stk (slots 2)) (stk (slots 3)) = stk := by
        rw [← source]
        simp [replaceFour, replaceThree, replaceTwo, Function.update_eq_self]
      simpa [finish] using Trace.step
        (show Within r (localConfig loop v stk) from bound) next (.refl _ bound)
  | cons a word ih =>
      cases supply : stk (slots 1) with
      | nil =>
          have next := clamp_stop P slots loop exit table v stk (Or.inr supply)
          have finish : replaceFour stk (slots 0) (slots 1) (slots 2) (slots 3)
              (a :: word) [] (stk (slots 2)) (stk (slots 3)) = stk := by
            rw [← source, ← supply]
            simp [replaceFour, replaceThree, replaceTwo, Function.update_eq_self]
          simpa [supply, finish] using Trace.step
            (show Within r (localConfig loop v stk) from bound) next (.refl _ bound)
      | cons b rest =>
          let middle := replaceFour stk (slots 0) (slots 1) (slots 2) (slots 3)
            word rest (a :: stk (slots 2)) (b :: stk (slots 3))
          have at₀ : middle (slots 0) = word := by
            simp [middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
          have at₁ : middle (slots 1) = rest := by
            simp [middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
          have at₂ : middle (slots 2) = a :: stk (slots 2) := by
            simp [middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
          have at₃ : middle (slots 3) = b :: stk (slots 3) := by simp [middle, replaceFour]
          have midBound : ∀ j, (middle j).length ≤ r := by
            apply replaceFour_bound stk _ _ _ _ r bound
            · have h := bound (slots 0); rw [source] at h; simp only [List.length_cons] at h; omega
            · have h := bound (slots 1); rw [supply] at h; simp only [List.length_cons] at h; omega
            · simp only [List.length_cons, supply] at destRoom ⊢; omega
            · simp only [List.length_cons, supply] at scratchRoom ⊢; omega
          have tail := ih middle midBound at₀
            (by simpa only [at₁, at₂, List.length_cons] using (show
              min word.length rest.length + ((stk (slots 2)).length + 1) ≤ r by
                simp only [supply, List.length_cons] at destRoom; omega))
            (by simpa only [at₁, at₃, List.length_cons] using (show
              min word.length rest.length + ((stk (slots 3)).length + 1) ≤ r by
                simp only [supply, List.length_cons] at scratchRoom; omega))
          have count : min (a :: word).length (b :: rest).length =
              min word.length rest.length + 1 := by simp [supply]
          simp only [at₁, at₂, at₃, middle, replaceFour_replace] at tail
          rw [count]
          simpa only [supply, List.drop_succ_cons, List.take_succ_cons,
            List.reverse_cons, List.append_assoc, List.singleton_append] using
            Trace.step (show Within r (localConfig loop v stk) from bound)
              (clamp_cons P slots loop exit table v stk a b word rest source supply) tail

include table in
/-- Extract a prefix whose length is controlled by a unary supply. Restore
that supply and the empty scratch stack, but retain the unread source suffix.
Unlike `clamp_all`, this routine can parse successive configuration fields. -/
theorem clamp_prefix (restore done : Q)
    (stop : exit = restore)
    (restoreTable : P restore = transferCode (slots 3) (slots 1) restore done (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S) (scratch : stk (slots 3) = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : min (stk (slots 0)).length (stk (slots 1)).length + (stk (slots 2)).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig done v (replaceTwo stk (slots 0) (slots 2)
        ((stk (slots 0)).drop (stk (slots 1)).length)
        (((stk (slots 0)).take (stk (slots 1)).length).reverse ++ stk (slots 2)))) := by
  subst exit
  let count := min (stk (slots 0)).length (stk (slots 1)).length
  let middle := replaceFour stk (slots 0) (slots 1) (slots 2) (slots 3)
    ((stk (slots 0)).drop count) ((stk (slots 1)).drop count)
    (((stk (slots 0)).take count).reverse ++ stk (slots 2))
    (((stk (slots 1)).take count).reverse ++ stk (slots 3))
  have first := clamp_scan P slots loop restore table v stk r bound room (by
    simp only [scratch, List.length_nil, Nat.add_zero]
    exact (Nat.min_le_right _ _).trans (bound (slots 1)))
  have supply : middle (slots 1) = (stk (slots 1)).drop count := by
    simp [middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
  have temporary : middle (slots 3) = ((stk (slots 1)).take count).reverse := by
    simp [middle, replaceFour, scratch]
  have restored := transfer_all P (slots 3) (slots 1) (slots_ne slots (by decide))
    restore done (fun _ => true) restoreTable v middle (by simp) r first.end_bound (by
      rw [supply, temporary]
      simp only [List.length_reverse, List.length_take, List.length_drop]
      have h := bound (slots 1)
      omega)
  let ready := replaceTwo stk (slots 0) (slots 2) ((stk (slots 0)).drop count)
    (((stk (slots 0)).take count).reverse ++ stk (slots 2))
  have restoredMemory : replaceTwo middle (slots 3) (slots 1) []
      ((middle (slots 3)).reverse ++ middle (slots 1)) = ready := by
    rw [temporary, supply, List.reverse_reverse, List.take_append_drop]
    funext j
    by_cases h₃ : j = slots 3
    · subst j; simp [ready, middle, replaceFour, replaceThree, replaceTwo, slots_ne slots, scratch]
    · by_cases h₂ : j = slots 2
      · subst j; simp [ready, middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
      · by_cases h₁ : j = slots 1
        · subst j; simp [ready, middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
        · by_cases h₀ : j = slots 0
          · subst j; simp [ready, middle, replaceFour, replaceThree, replaceTwo, slots_ne slots]
          · simp [ready, middle, replaceFour, replaceThree, replaceTwo, h₀, h₁, h₂, h₃]
  rw [restoredMemory] at restored
  have take : (stk (slots 0)).take count = (stk (slots 0)).take (stk (slots 1)).length := by
    dsimp [count]
    by_cases h : (stk (slots 0)).length ≤ (stk (slots 1)).length
    · rw [Nat.min_eq_left h, List.take_length, List.take_of_length_le h]
    · rw [Nat.min_eq_right (by omega)]
  have drop : (stk (slots 0)).drop count = (stk (slots 0)).drop (stk (slots 1)).length := by
    dsimp [count]
    by_cases h : (stk (slots 0)).length ≤ (stk (slots 1)).length
    · rw [Nat.min_eq_left h, List.drop_length, List.drop_eq_nil_of_le h]
    · rw [Nat.min_eq_right (by omega)]
  simpa only [ready, take, drop] using first.trans restored

include table in
/-- Clamp the source to the supply length, empty the unused suffix, and
restore the entire supply. The scratch stack is empty again on return. -/
theorem clamp_all (restore clear done : Q)
    (stop : exit = restore)
    (restoreTable : P restore = transferCode (slots 3) (slots 1) restore clear (fun _ => true))
    (clearTable : P clear = clearCode (slots 0) clear done (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S) (scratch : stk (slots 3) = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : min (stk (slots 0)).length (stk (slots 1)).length + (stk (slots 2)).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig done v (replaceTwo stk (slots 0) (slots 2) []
        (((stk (slots 0)).take (stk (slots 1)).length).reverse ++ stk (slots 2)))) := by
  have first := clamp_prefix P slots loop exit table restore clear stop restoreTable
    v stk scratch r bound room
  let ready := replaceTwo stk (slots 0) (slots 2)
    ((stk (slots 0)).drop (stk (slots 1)).length)
    (((stk (slots 0)).take (stk (slots 1)).length).reverse ++ stk (slots 2))
  have last := clear_all P (slots 0) clear done (fun _ => true) clearTable v ready (by simp)
    r first.end_bound
  have finish : Function.update ready (slots 0) [] = replaceTwo stk (slots 0) (slots 2) []
      (((stk (slots 0)).take (stk (slots 1)).length).reverse ++ stk (slots 2)) := by
    funext j
    by_cases h₀ : j = slots 0
    · subst j; simp [replaceTwo, slots_ne slots]
    · by_cases h₂ : j = slots 2 <;> simp [ready, replaceTwo, h₀, h₂]
  rw [finish] at last
  exact first.trans last

end ComplexityOfGenerators.Simulation.StackSpace
