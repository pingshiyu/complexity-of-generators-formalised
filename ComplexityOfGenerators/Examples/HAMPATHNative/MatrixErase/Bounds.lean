import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixErase.Components
import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixErase.Model

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem transfer_empty_bound {O : Type} (src dst : Fin 32) (different : src ≠ dst) (s : Store)
    (budget : ℕ) (sizes : StoreBound s budget) (empty : s dst = []) :
    StoreBound ((Routine.transfer (O := O) src dst different id).eval s) budget := by
  change StoreBound (Function.update (Function.update s src []) dst ((s src).reverse.map id ++ s dst)) budget
  apply (sizes.clear src).update dst
  simpa [empty] using sizes src

theorem rowPrepare_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((rowPrepare (O := O)).eval s) budget ∧
      (rowPrepare (O := O)).cost s ≤ 110 * (budget + 1) := by
  let a := (Routine.clearMany (O := O) [30, 31]).eval s
  let b := (Routine.assign (O := O) 27 10 9 (by decide) (by decide) (by decide) id).eval a
  let c := (Blocks.routine (O := O) 10 2 30 (by decide) (by decide)).eval b
  let d := (Routine.transfer (O := O) 30 31 (by decide) id).eval c
  have aBound : StoreBound a budget := sizes.clearMany [30, 31]
  have bBound : StoreBound b budget := aBound.assign 27 10 9 (by decide) (by decide) (by decide) id
  have bEmpty : b 30 = [] := by simp [b, a, Routine.assign_eval, Routine.clearMany_eval]
  have cBound : StoreBound c budget := bBound.block 10 2 30 (by decide) (by decide) (by decide) bEmpty
  have cEmpty : c 31 = [] := by
    simp [c, b, a, Blocks.routine_eval, Routine.assign_eval, Routine.clearMany_eval]
  have dBound : StoreBound d budget := transfer_empty_bound 30 31 (by decide) c budget cBound cEmpty
  have finalBound := DropAt.routine_bound (O := O) columnSlots (.bit true) d budget dBound
  constructor
  · exact finalBound
  · have clearCost := Routine.clearMany_cost (O := O) ([30, 31] : List (Fin 32)) s budget
      (by intro j _; exact sizes j)
    have assignCost : (Routine.assign (O := O) 27 10 9 (by decide) (by decide) (by decide) id).cost a ≤
        20 * budget + 3 := by
      rw [Routine.assign_cost]
      have source := aBound 27
      have target := aBound 10
      have scratch := aBound 9
      omega
    have blockCost := Blocks.routine_cost (O := O) (10 : Fin 32) 2 30 (by decide) (by decide) b
    have transferCost : (Routine.transfer (O := O) 30 31 (by decide) id).cost c ≤ 6 * budget := by
      change 6 * (c 30).length ≤ _
      exact Nat.mul_le_mul_left 6 (cBound 30)
    have eraseCost := DropAt.routine_cost (O := O) columnSlots (.bit true) d budget dBound
    have clock := bBound 10
    simp only [List.length_cons, List.length_nil] at clearCost
    change (Routine.clearMany (O := O) [30, 31]).cost s + 1 +
      ((Routine.assign (O := O) 27 10 9 (by decide) (by decide) (by decide) id).cost a + 1 +
        ((Blocks.routine (O := O) 10 2 30 (by decide) (by decide)).cost b + 1 +
          ((Routine.transfer (O := O) 30 31 (by decide) id).cost c + 1 +
            (DropAt.routine (O := O) columnSlots (.bit true)).cost d))) ≤ _
    omega

theorem rowChoose_cost {O : Type} (s : Store) :
    (rowChoose (O := O)).cost s ≤ 6 * (s 31).length + 2 := by
  cases count : s 7 <;> cases pending : s 13 <;>
    simp [rowChoose, Routine.branch, Routine.transfer, Routine.clear, count, pending] <;> omega

theorem advance_ticks (s : Store) : advance.ticks s ≤ 2 := by
  cases count : s 7 <;> simp [advance, Local.ticks, Local.pop, count]

theorem rowRoutine_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (rowRoutine (O := O)).cost s ≤ 120 * (budget + 1) := by
  let a := (rowPrepare (O := O)).eval s
  let b := (rowChoose (O := O)).eval a
  obtain ⟨preparedBound, preparedCost⟩ := rowPrepare_bound (O := O) s budget sizes
  have selected := rowChoose_cost (O := O) a
  have finalCost := advance_ticks b
  have rowSize := preparedBound 31
  change (rowPrepare (O := O)).cost s + 1 + ((rowChoose (O := O)).cost a + 1 + advance.ticks b) ≤ _
  change (a 31).length ≤ budget at rowSize
  omega

theorem encoded_bound (base : Store) (size start : ℕ) (state : State) (clock : List Symbol)
    (budget : ℕ) (baseBound : StoreBound base budget) (sizeBound : size ≤ budget) (startBound : start ≤ budget)
    (counterBound : state.countdown ≤ budget) (clockBound : clock.length ≤ budget)
    (measure : state.word.length + state.outRev.length ≤ budget) :
    StoreBound (encoded base size start state clock) (budget + 1) := by
  intro j
  fin_cases j <;> simp [encoded, flag] <;>
    (try split) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact (baseBound _).trans (by omega) | omega

theorem rows_cost {O : Type} (base : Store) (size start : ℕ) (state : State) (count budget : ℕ)
    (baseBound : StoreBound base budget) (sizeBound : size ≤ budget) (startBound : start ≤ budget)
    (counterBound : state.countdown ≤ budget) (countBound : count ≤ budget)
    (measure : state.word.length + state.outRev.length ≤ budget) :
    (rows (O := O)).cost (encoded base size start state (List.replicate count (.bit true))) ≤
      count * (200 * (budget + 2)) := by
  have bounded := Routine.loopCost_bound (counted (O := O)).cost (counted (O := O)).eval
    count (120 * (budget + 2) + 2) (encoded base size start state (List.replicate count (.bit true))) (by
      intro i inside
      rw [iterate_eval]
      let next := (step size start)^[i] state
      let remaining := (List.replicate count (Symbol.bit true)).drop i
      have nextCounter : next.countdown ≤ budget := by
        rw [show next.countdown = state.countdown - i from iterate_countdown size start i state]
        omega
      have nextMeasure : next.word.length + next.outRev.length ≤ budget :=
        (iterate_measure size start i state).trans measure
      have clockSize : remaining.tail.length ≤ budget := by
        simp [remaining, List.length_tail, List.length_drop]
        omega
      have stateBound := encoded_bound base size start next remaining.tail budget baseBound sizeBound startBound
        nextCounter clockSize nextMeasure
      have cost := rowRoutine_cost (O := O) (encoded base size start next remaining.tail) (budget + 1) stateBound
      change 1 + 1 + (rowRoutine (O := O)).cost
        ((Local.pop (S := Symbol) (5 : Fin 32)).eval (encoded base size start next remaining)) ≤ _
      rw [show (Local.pop (S := Symbol) (5 : Fin 32)).eval (encoded base size start next remaining) =
          encoded base size start next remaining.tail by
        funext j; fin_cases j <;> simp [Local.eval_pop, encoded]]
      omega)
  change Routine.loopCost (counted (O := O)).cost (counted (O := O)).eval
    ((encoded base size start state (List.replicate count (.bit true))) 5).length _ ≤ _
  rw [show encoded base size start state (List.replicate count (.bit true)) 5 = List.replicate count (.bit true) by simp [encoded]]
  simp only [List.length_replicate]
  apply bounded.trans
  apply Nat.mul_le_mul_left
  omega

theorem rowChoose_randomFree {O : Type} : Command.RandomFree (rowChoose (O := O)).command := by
  simp only [rowChoose, Routine.randomFree_branch]
  intro head
  split
  · simp
  · simp only [Routine.randomFree_branch]
    intro pending
    split <;> simp

theorem rows_randomFree {O : Type} : Command.RandomFree (rows (O := O)).command := by
  simp [rows, rowRoutine, rowPrepare, rowChoose_randomFree, Blocks.routine, Blocks.body, DropAt.routine_randomFree]

end ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase
