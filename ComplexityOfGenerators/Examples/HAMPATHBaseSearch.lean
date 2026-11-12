import ComplexityOfGenerators.Examples.HAMPATHAncestors
import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
import ComplexityOfGenerators.Simulation.WordStack.LengthTest
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops
import Mathlib.Tactic.FinCases

/-! A native stack search for productive HAMPATH target lengths. It examines
k=1,...,n, constructs f(k)=(k+1)^2+1 with verified unary routines, and remembers
whether a match occurred. Every register operation is a primitive command. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.BaseSearch

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Unit 12

def square : PolynomialBound := ⟨1, 2, by omega⟩

def counterSlots : CounterRoutine.Layout 12 where
  toFun := fun j => ⟨j.val + 2, by omega⟩
  inj' := by
    intro j k equal
    apply Fin.ext
    have := congrArg Fin.val equal
    change j.val + 2 = k.val + 2 at this
    omega

def lengthSlots : LengthTest.Layout 12 := ⟨![3, 0, 7, 8, 9, 6], by decide⟩

def remember : Local Unit 12 :=
  .read 7 fun flag => if flag.isSome then Local.write 11 () else .skip

def body : Routine Unit Symbol 12 :=
  (Routine.ofLocal (Local.push 2 ())).seq
  ((CounterRoutine.routine counterSlots square ()).seq
  ((Routine.ofLocal (Local.push 3 ())).seq
  ((LengthTest.routine lengthSlots ()).seq (Routine.ofLocal remember))))

theorem remember_eval (s : Store) : remember.eval s =
    Function.update s 11 (if (s 7).head?.isSome then () :: (s 11).tail else s 11) := by
  by_cases flag : (s 7).head?.isSome
  · simp [remember, Local.eval_read, flag, Local.eval_write]
  · simp [remember, Local.eval_read, flag, Function.update_eq_self]

theorem body_eval_candidate (s : Store) : body.eval s 2 = () :: s 2 := by
  simp [body, Routine.seq, Routine.ofLocal, CounterRoutine.routine_eval,
    LengthTest.routine_eval, remember_eval, counterSlots, lengthSlots]

theorem body_eval_target (s : Store) : body.eval s 0 = s 0 := by
  simp [body, Routine.seq, Routine.ofLocal, CounterRoutine.routine_eval,
    LengthTest.routine_eval, remember_eval, counterSlots, lengthSlots]

theorem body_eval_clock (s : Store) : body.eval s 1 = s 1 := by
  simp [body, Routine.seq, Routine.ofLocal, CounterRoutine.routine_eval,
    LengthTest.routine_eval, remember_eval, counterSlots, lengthSlots]

theorem body_eval_found (s : Store) : body.eval s 11 =
    if encodingLength ((s 2).length + 1) = (s 0).length then () :: (s 11).tail else s 11 := by
  have polynomial : square ((s 2).length + 1) + 1 = encodingLength ((s 2).length + 1) := by
    simp only [square, PolynomialBound.eval, encodingLength]
    ring
  simp [body, Routine.seq, Routine.ofLocal, CounterRoutine.routine_eval,
    LengthTest.routine_eval, remember_eval, counterSlots, lengthSlots,
    List.length_cons, polynomial]

def counted : Routine Unit Symbol 12 := Routine.counted 1 body

theorem counted_candidate (s : Store) : counted.eval s 2 = () :: s 2 := by
  simp [counted, Routine.counted, Routine.seq, Routine.ofLocal, body_eval_candidate]

theorem counted_target (s : Store) : counted.eval s 0 = s 0 := by
  simp [counted, Routine.counted, Routine.seq, Routine.ofLocal, body_eval_target]

theorem counted_found (s : Store) : counted.eval s 11 =
    if encodingLength ((s 2).length + 1) = (s 0).length then () :: (s 11).tail else s 11 := by
  simp [counted, Routine.counted, Routine.seq, Routine.ofLocal, body_eval_found]

theorem counted_clock (s : Store) : counted.eval s 1 = (s 1).tail :=
  Routine.counted_clock 1 body body_eval_clock s

def initialStore (n : ℕ) : Store :=
  Function.update (Function.update (fun _ => []) 0 (List.replicate n ())) 1 (List.replicate n ())

theorem iterate_candidate (n steps : ℕ) :
    (counted.eval^[steps] (initialStore n)) 2 = List.replicate steps () := by
  induction steps with
  | zero => simp [initialStore]
  | succ steps ih => rw [Function.iterate_succ_apply', counted_candidate, ih]; rfl

theorem iterate_target (n steps : ℕ) :
    (counted.eval^[steps] (initialStore n)) 0 = List.replicate n () := by
  induction steps with
  | zero => simp [initialStore]
  | succ steps ih => rw [Function.iterate_succ_apply', counted_target, ih]

theorem iterate_clock (n steps : ℕ) :
    (counted.eval^[steps] (initialStore n)) 1 = List.replicate (n - steps) () := by
  induction steps with
  | zero => simp [initialStore]
  | succ steps ih => rw [Function.iterate_succ_apply', counted_clock, ih]; simp; omega

theorem iterate_found (n steps : ℕ) :
    (counted.eval^[steps] (initialStore n)) 11 =
      if ∃ k ≤ steps, 1 ≤ k ∧ encodingLength k = n then [()] else [] := by
  induction steps with
  | zero => simp [initialStore]
  | succ steps ih =>
    rw [Function.iterate_succ_apply', counted_found, iterate_candidate, iterate_target]
    simp only [List.length_replicate]
    rw [ih]
    by_cases matchNow : encodingLength (steps + 1) = n
    · have existsNow : ∃ k ≤ steps + 1, 1 ≤ k ∧ encodingLength k = n :=
        ⟨steps + 1, le_rfl, by omega, matchNow⟩
      by_cases previous : ∃ k ≤ steps, 1 ≤ k ∧ encodingLength k = n <;>
        simp [matchNow, previous, existsNow]
    · rw [ite_eq_right matchNow]
      have equivalent : (∃ k ≤ steps + 1, 1 ≤ k ∧ encodingLength k = n) ↔
          ∃ k ≤ steps, 1 ≤ k ∧ encodingLength k = n := by
        constructor
        · rintro ⟨k, bound, positive, equal⟩
          refine ⟨k, ?_, positive, equal⟩
          by_contra larger
          have : k = steps + 1 := by omega
          subst k
          contradiction
        · rintro ⟨k, bound, positive, equal⟩
          exact ⟨k, by omega, positive, equal⟩
      simp only [equivalent]

def search : Routine Unit Symbol 12 := Routine.iterate 1 body body_eval_clock

theorem search_found (n : ℕ) : (search.eval (initialStore n) 11).head?.isSome =
    decide (∃ k ≤ n, 1 ≤ k ∧ encodingLength k = n) := by
  simp only [search, Routine.iterate, initialStore, Function.update_self, List.length_replicate]
  change ((counted.eval^[n] (initialStore n)) 11).head?.isSome = _
  rw [iterate_found]
  split_ifs <;> simp_all

def storeBudget (n : ℕ) : ℕ := encodingLength n + 1

theorem storeBudget_large (n : ℕ) : n + 2 ≤ storeBudget n := by
  unfold storeBudget encodingLength
  omega

theorem body_store_bound (n : ℕ) (s : Store)
    (sizes : ∀ j, (s j).length ≤ storeBudget n) (candidate : (s 2).length + 1 ≤ n) :
    ∀ j, (body.eval s j).length ≤ storeBudget n := by
  have source := sizes 0
  have clock := sizes 1
  have unused := sizes 10
  have found := sizes 11
  have large := storeBudget_large n
  have baseBound : (s 2).length + 2 ≤ storeBudget n := by omega
  have squareBound : square ((s 2).length + 1) + 1 ≤ storeBudget n := by
    have polynomial : square ((s 2).length + 1) + 1 = encodingLength ((s 2).length + 1) := by
      simp only [square, PolynomialBound.eval, encodingLength]
      ring
    rw [polynomial]
    exact (encodingLength_strictMono.monotone candidate).trans (Nat.le_succ _)
  intro j
  fin_cases j <;>
    simp [body, Routine.seq, Routine.ofLocal, CounterRoutine.routine_eval,
      LengthTest.routine_eval, remember_eval, counterSlots, lengthSlots] <;>
    (try split_ifs) <;> (try simp only [List.length_cons, List.length_nil, List.length_tail]) <;> omega

theorem counted_store_bound (n : ℕ) (s : Store)
    (sizes : ∀ j, (s j).length ≤ storeBudget n) (candidate : (s 2).length + 1 ≤ n) :
    ∀ j, (counted.eval s j).length ≤ storeBudget n := by
  apply body_store_bound n (Function.update s 1 (s 1).tail)
  · intro j
    by_cases clock : j = 1
    · subst j; simp only [Function.update_self, List.length_tail]; have := sizes 1; omega
    · simpa [clock] using sizes j
  · simpa using candidate

theorem iterate_store_bound (n steps : ℕ) (bound : steps ≤ n) :
    ∀ j, ((counted.eval^[steps] (initialStore n)) j).length ≤ storeBudget n := by
  induction steps with
  | zero =>
    intro j
    have large := storeBudget_large n
    simp only [Function.iterate_zero, id_eq, initialStore]
    by_cases zero : j = 0 <;> by_cases one : j = 1 <;> simp [zero, one] <;> omega
  | succ steps ih =>
    rw [Function.iterate_succ_apply']
    apply counted_store_bound n _ (ih (by omega))
    rw [iterate_candidate]
    simpa using bound

theorem remember_cost (s : Store) : remember.ticks s ≤ 4 := by
  cases flag : (s 7).head? <;>
    simp [remember, Local.ticks, Local.write, Local.pop, Local.push, flag]

noncomputable def bodyBudget (n : ℕ) : ℕ := 120 * (storeBudget n + 1) + Command.counterBudget square n

theorem body_cost (n : ℕ) (s : Store)
    (sizes : ∀ j, (s j).length ≤ storeBudget n) (candidate : (s 2).length + 1 ≤ n) :
    body.cost s ≤ bodyBudget n := by
  let first : Store := Function.update s 2 (() :: s 2)
  let second : Store := (CounterRoutine.routine (O := Symbol) counterSlots square ()).eval first
  let third : Store := Function.update second 3 (() :: second 3)
  let last : Store := (LengthTest.routine (O := Symbol) lengthSlots ()).eval third
  have large := storeBudget_large n
  have baseBound : (s 2).length + 2 ≤ storeBudget n := by omega
  have squareBound : square ((s 2).length + 1) + 1 ≤ storeBudget n := by
    have polynomial : square ((s 2).length + 1) + 1 = encodingLength ((s 2).length + 1) := by
      simp only [square, PolynomialBound.eval, encodingLength]
      ring
    rw [polynomial]
    exact (encodingLength_strictMono.monotone candidate).trans (Nat.le_succ _)
  have firstSizes : ∀ j, (first j).length ≤ storeBudget n := by
    intro j
    by_cases same : j = 2
    · subst j; simp [first]; omega
    · simpa [first, same] using sizes j
  have secondSizes : ∀ j, (second j).length ≤ storeBudget n := by
    intro j
    fin_cases j <;>
      simp [second, CounterRoutine.routine_eval, counterSlots, first] <;>
      first | exact sizes _ | omega
  have thirdSizes : ∀ j, (third j).length ≤ storeBudget n := by
    intro j
    by_cases same : j = 3
    · subst j
      simp [third, second, CounterRoutine.routine_eval, counterSlots, first]
      omega
    · simpa [third, same] using secondSizes j
  have counterCost := CounterRoutine.routine_cost (O := Symbol) counterSlots square () first
    (storeBudget n) firstSizes
  have lengthCost := LengthTest.routine_cost (O := Symbol) lengthSlots () third
    (storeBudget n) thirdSizes
  have finalCost := remember_cost last
  have counterMono : Command.counterBudget square (first 2).length ≤ Command.counterBudget square n := by
    apply Nat.mul_le_mul_left
    apply pow_le_pow_left'
    simpa [first] using Nat.add_le_add_right candidate 1
  change 1 + 1 + ((CounterRoutine.routine (O := Symbol) counterSlots square ()).cost first + 1 +
    (1 + 1 + ((LengthTest.routine (O := Symbol) lengthSlots ()).cost third + 1 +
      remember.ticks last))) ≤ _
  change (CounterRoutine.routine (O := Symbol) counterSlots square ()).cost first ≤
    26 * storeBudget n + 7 + Command.counterBudget square (first 2).length at counterCost
  unfold bodyBudget
  omega

theorem counted_cost (n : ℕ) (s : Store)
    (sizes : ∀ j, (s j).length ≤ storeBudget n) (candidate : (s 2).length + 1 ≤ n) :
    counted.cost s ≤ bodyBudget n + 2 := by
  have bound := body_cost n (Function.update s 1 (s 1).tail) (by
    intro j
    by_cases clock : j = 1
    · subst j; simp only [Function.update_self, List.length_tail]; have := sizes 1; omega
    · simpa [clock] using sizes j) (by simpa using candidate)
  change 1 + 1 + body.cost (Function.update s 1 (s 1).tail) ≤ _
  omega

theorem search_cost (n : ℕ) : search.cost (initialStore n) ≤ n * (bodyBudget n + 4) := by
  have bound := Routine.loopCost_bound counted.cost counted.eval n (bodyBudget n + 2) (initialStore n) (by
    intro i hi
    apply counted_cost n _ (iterate_store_bound n i (by omega))
    rw [iterate_candidate]
    simpa using (show i + 1 ≤ n by omega))
  simpa [search, Routine.iterate, initialStore, counted, Nat.add_assoc] using bound

end ComplexityOfGenerators.Examples.HAMPATH.BaseSearch
