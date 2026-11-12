import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Components

set_option maxHeartbeats 1600000

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

structure Stored (n j : ℕ) (candidate : Option (List α)) (bits : BitString) (s : Store G H) : Prop where
  input : s 11 = []
  auxiliary : s 12 = []
  empty : s 14 = []
  master : (s 22).length = n
  leftIndex : (s 23).length = j
  rightIndex : (s 24).length = n - j
  random : s 17 = bits.map Symbol.bit
  candidateWord : s 31 = UnionGenerator.held G H candidate
  found : s 32 = UnionGenerator.flagWord G H candidate.isSome

structure PairStored (n j : ℕ) (candidate left right : Option (List α)) (bits : BitString)
    (s : Store G H) extends Stored G H n j candidate bits s : Prop where
  leftWord : s 25 = UnionGenerator.held G H left
  leftFlag : s 27 = UnionGenerator.flagWord G H left.isSome
  rightWord : s 26 = UnionGenerator.held G H right
  rightFlag : s 28 = UnionGenerator.flagWord G H right.isSome

theorem sourceTrial_fixes_outer {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell G H) (decode : Cell G H → Source.Symbol M)
    (f g b : Cell G H → Cell G H) (seed time : PolynomialBound)
    (j : Fin 35) (outer : 22 ≤ j.val) :
    (BoundedSource.sourceTrial (Symbol.unit : Cell G H) Symbol.bit M encode decode f g b seed time).Fixes j := by
  intro s
  have ne (r : ℕ) (small : r < 22) : j.val ≠ r := by omega
  simpa [BoundedSource.trialPrepared, show j ≠ 14 by omega, show j ≠ 15 by omega,
    show j ≠ 16 by omega, show j ≠ 17 by omega, show j ≠ 18 by omega,
    show j ≠ 19 by omega, show j ≠ 20 by omega, show j ≠ 21 by omega] using
    BoundedSource.sourceTrial_outside (O := α) (Symbol.unit : Cell G H) Symbol.bit M encode decode f g b
      seed time s j (by omega) (by omega)

theorem leftFinish_fixes_outer (j : Fin 35) (outer : 22 ≤ j.val) (word : j ≠ 25) (flag : j ≠ 27) :
    (UnionGenerator.leftFinish G H).Fixes j := by
  intro s
  have output : j ≠ 10 := by omega
  simp only [UnionGenerator.leftFinish, WordStack.Routine.branch]
  split <;> simp [WordStack.Routine.seq, UnionGenerator.takeOutput_eval, UnionGenerator.flag_eval,
    WordStack.Routine.clear, word, flag, output]

theorem rightFinish_fixes_outer (j : Fin 35) (outer : 22 ≤ j.val) (word : j ≠ 26) (flag : j ≠ 28) :
    (UnionGenerator.rightFinish G H).Fixes j := by
  intro s
  have output : j ≠ 10 := by omega
  simp only [UnionGenerator.rightFinish, WordStack.Routine.branch]
  split <;> simp [WordStack.Routine.seq, UnionGenerator.takeOutput_eval, UnionGenerator.flag_eval,
    WordStack.Routine.clear, word, flag, output]

theorem leftStep_frame (seed time : PolynomialBound) (s : Store G H)
    (r : Fin 35) (outer : 22 ≤ r.val) (word : r ≠ 25) (flag : r ≠ 27) :
    (UnionGenerator.leftFinish G H).eval ((UnionGenerator.leftTrial G H seed time).eval s) r = s r := by
  exact ((sourceTrial_fixes_outer G H G Symbol.left (UnionGenerator.leftDecode G H)
    (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit G H) seed time r outer).seq
    (leftFinish_fixes_outer G H r outer word flag)) s

theorem rightStep_frame (seed time : PolynomialBound) (s : Store G H)
    (r : Fin 35) (outer : 22 ≤ r.val) (word : r ≠ 26) (flag : r ≠ 28) :
    (UnionGenerator.rightFinish G H).eval ((UnionGenerator.rightTrial G H seed time).eval s) r = s r := by
  exact ((sourceTrial_fixes_outer G H H Symbol.right (UnionGenerator.rightDecode G H)
    (fun _ => .right .unit) (fun _ => .right .unit) (UnionGenerator.rightBit G H) seed time r outer).seq
    (rightFinish_fixes_outer G H r outer word flag)) s

theorem reset_eval (s : Store G H) :
    (reset G H).eval s = Function.update (Function.update
      (Function.update (Function.update s 25 []) 26 []) 27 []) 28 [] := by
  simp [reset, WordStack.Routine.seq, WordStack.Routine.clear, UnionGenerator.flag_eval, UnionGenerator.flagWord]

theorem save_eval (s : Store G H) :
    (save G H).eval s = Function.update (Function.update (Function.update s 33 [])
      31 (s 25 ++ s 26)) 32 [Symbol.unit] := by
  funext j
  fin_cases j <;>
    simp [save, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.copy,
      UnionGenerator.flag_eval, UnionGenerator.flagWord]

theorem offerStored_correct (n j : ℕ) (previous left right : Option (List α)) (bits : BitString)
    (s : Store G H) (stored : PairStored G H n j previous left right bits s) :
    Stored G H n (j + 1)
      (offer previous (pairValue left right) (bits.head? == some true)) (bits.drop 1)
      ((advance G H).eval ((offerStored G H).eval s)) := by
  rcases stored with ⟨⟨input, auxiliary, empty, master, li, ri, random, previousWord, previousFlag⟩,
    leftWord, leftFlag, rightWord, rightFlag⟩
  have tailIndex : (s 24).tail.length = n - (j + 1) := by
    simp only [List.length_tail, ri]
    omega
  cases bits with
  | nil =>
    cases previous <;> cases left <;> cases right <;>
      constructor <;>
      simp [offerStored, advance, offer, pairValue, WordStack.Routine.branch,
        WordStack.Routine.seq, WordStack.Routine.skip, WordStack.Routine.ofLocal,
        Local.eval_pop, Local.eval_push, save_eval, previousWord, previousFlag, leftWord, leftFlag,
        rightWord, rightFlag, random, input, auxiliary, empty, master, li, tailIndex,
        UnionGenerator.held, UnionGenerator.flagWord, UnionGenerator.letters, List.map_append, Option.or]
  | cons bit rest =>
    cases bit <;> cases previous <;> cases left <;> cases right <;>
      constructor <;>
      simp [offerStored, advance, offer, pairValue, WordStack.Routine.branch,
        WordStack.Routine.seq, WordStack.Routine.skip, WordStack.Routine.ofLocal,
        Local.eval_pop, Local.eval_push, save_eval, previousWord, previousFlag, leftWord, leftFlag,
        rightWord, rightFlag, random, input, auxiliary, empty, master, li, tailIndex,
        UnionGenerator.held, UnionGenerator.flagWord, UnionGenerator.letters, List.map_append, Option.or]

theorem splitStep_correct (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (previous : Option (List α)) (bits : BitString) (s : Store G H)
    (stored : Stored G H n j previous bits s) :
    Stored G H n (j + 1)
      (next G H leftSeed leftTime rightSeed rightTime n j (previous, bits)).1
      (next G H leftSeed leftTime rightSeed rightTime n j (previous, bits)).2
      ((splitStep G H leftSeed leftTime rightSeed rightTime).eval s) := by
  let a := (WordStack.Routine.assign (O := α) 23 13 33 (by decide) (by decide) (by decide) id).eval
    ((reset G H).eval s)
  have initial : UnionGenerator.Stored G H j bits none none a := by
    constructor <;> simp [a, WordStack.Routine.assign_eval, reset_eval, UnionGenerator.held,
      UnionGenerator.flagWord, stored.input, stored.auxiliary, stored.empty, stored.leftIndex, stored.random]
  let b := (UnionGenerator.leftFinish G H).eval ((UnionGenerator.leftTrial G H leftSeed leftTime).eval a)
  have left := UnionGenerator.leftStep_stored G H leftSeed leftTime j bits none none a initial
  have b_outer (r : Fin 35) (allowed : r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 31 ∨ r = 32) : b r = s r := by
    have large : 22 ≤ r.val := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have nw : r ≠ 25 := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have nf : r ≠ 27 := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have frame := (sourceTrial_fixes_outer G H G Symbol.left (UnionGenerator.leftDecode G H)
      (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit G H) leftSeed leftTime r large).seq
      (leftFinish_fixes_outer G H r large nw nf)
    have first : b r = a r := frame a
    rw [first]
    rcases allowed with rfl | rfl | rfl | rfl | rfl <;>
      simp [a, WordStack.Routine.assign_eval, reset_eval]
  let c := (WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).eval b
  have middle : UnionGenerator.Stored G H (n - j) (bits.drop (leftSeed j))
      (UnionGenerator.sourceValue G leftTime j (bits.take (leftSeed j))) none c := by
    constructor
    · simpa [c, WordStack.Routine.assign_eval] using left.input
    · simpa [c, WordStack.Routine.assign_eval] using left.auxiliary
    · simpa [c, WordStack.Routine.assign_eval, b_outer 24 (by simp)] using stored.rightIndex
    · simpa [c, WordStack.Routine.assign_eval] using left.random
    · simpa [c, WordStack.Routine.assign_eval] using left.empty
    · simpa [c, WordStack.Routine.assign_eval] using left.leftWord
    · simpa [c, WordStack.Routine.assign_eval] using left.leftFlag
    · simpa [c, WordStack.Routine.assign_eval] using left.rightWord
    · simpa [c, WordStack.Routine.assign_eval] using left.rightFlag
  let d := (UnionGenerator.rightFinish G H).eval ((UnionGenerator.rightTrial G H rightSeed rightTime).eval c)
  have right := UnionGenerator.rightStep_stored G H rightSeed rightTime (n - j) (bits.drop (leftSeed j))
    (UnionGenerator.sourceValue G leftTime j (bits.take (leftSeed j))) none c middle
  have d_outer (r : Fin 35) (allowed : r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 31 ∨ r = 32) : d r = s r := by
    have large : 22 ≤ r.val := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have nw : r ≠ 26 := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have nf : r ≠ 28 := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have frame := (sourceTrial_fixes_outer G H H Symbol.right (UnionGenerator.rightDecode G H)
      (fun _ => .right .unit) (fun _ => .right .unit) (UnionGenerator.rightBit G H) rightSeed rightTime r large).seq
      (rightFinish_fixes_outer G H r large nw nf)
    have first : d r = c r := frame c
    rw [first]
    have second : c r = b r := by
      rcases allowed with rfl | rfl | rfl | rfl | rfl <;> simp [c, WordStack.Routine.assign_eval]
    rw [second]
    exact b_outer r allowed
  have pair : PairStored G H n j previous
      (UnionGenerator.sourceValue G leftTime j (bits.take (leftSeed j)))
      (UnionGenerator.sourceValue H rightTime (n - j) ((bits.drop (leftSeed j)).take (rightSeed (n - j))))
      ((bits.drop (leftSeed j)).drop (rightSeed (n - j))) d := by
    constructor
    · constructor
      · exact right.input
      · exact right.auxiliary
      · exact right.empty
      · simpa [d_outer 22 (by simp)] using stored.master
      · simpa [d_outer 23 (by simp)] using stored.leftIndex
      · simpa [d_outer 24 (by simp)] using stored.rightIndex
      · exact right.random
      · simpa [d_outer 31 (by simp)] using stored.candidateWord
      · simpa [d_outer 32 (by simp)] using stored.found
    · exact right.leftWord
    · exact right.leftFlag
    · exact right.rightWord
    · exact right.rightFlag
  have answer := offerStored_correct G H n j previous _ _ _ d pair
  simpa only [splitStep, WordStack.Routine.seq, next, List.drop_drop, a, b, c, d] using answer

theorem Stored.pop_clock {n j : ℕ} {previous : Option (List α)} {bits : BitString} {s : Store G H}
    (stored : Stored G H n j previous bits s) :
    Stored G H n j previous bits ((Local.pop (30 : Fin 35)).eval s) := by
  rcases stored with ⟨input, auxiliary, empty, master, li, ri, random, word, found⟩
  constructor <;> simp_all [Local.eval_pop]

theorem loop_correct (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n steps j : ℕ) (p : Option (List α) × BitString) (s : Store G H)
    (stored : Stored G H n j p.1 p.2 s) :
    let answer := (List.range' j steps).foldl
      (fun p j => next G H leftSeed leftTime rightSeed rightTime n j p) p
    Stored G H n (j + steps) answer.1 answer.2
      ((WordStack.Routine.counted 30 (splitStep G H leftSeed leftTime rightSeed rightTime)).eval^[steps] s) := by
  induction steps generalizing j p s with
  | zero => simpa using stored
  | succ steps ih =>
    have nextView := splitStep_correct G H leftSeed leftTime rightSeed rightTime n j p.1 p.2
      ((Local.pop (30 : Fin 35)).eval s) stored.pop_clock
    have last := ih (j + 1) (next G H leftSeed leftTime rightSeed rightTime n j p) _ nextView
    simpa only [List.range'_succ, List.foldl_cons, Function.iterate_succ_apply,
      WordStack.Routine.counted, WordStack.Routine.seq, WordStack.Routine.ofLocal,
      Nat.add_assoc, Nat.add_comm 1 steps] using last

structure Chosen (n : ℕ) (answer : Option (List α)) (s : Store G H) : Prop where
  index : (s 13).length = n
  word : s 31 = UnionGenerator.held G H answer
  found : s 32 = UnionGenerator.flagWord G H answer.isSome

theorem body_chosen (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n read : ℕ) (bits : BitString) :
    Chosen G H n (algorithm G H leftSeed leftTime rightSeed rightTime n bits)
      ((body G H leftSeed leftTime rightSeed rightTime).eval
        (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store) := by
  let start := (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store
  let ready := (setup G H).eval start
  have initial : Stored G H n 0 none bits ready := by
    constructor <;>
      simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.ofLocal, Local.eval_push, BoundedSource.preparedMemory,
        UnionGenerator.held, UnionGenerator.flagWord]
  have clock : (ready 30).length = n + 1 := by
    simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
      WordStack.Routine.ofLocal, Local.eval_push, BoundedSource.preparedMemory]
  have last := loop_correct G H leftSeed leftTime rightSeed rightTime n (n + 1) 0 (none, bits) ready initial
  let endStore := (WordStack.Routine.counted 30
    (splitStep G H leftSeed leftTime rightSeed rightTime)).eval^[n + 1] ready
  have result : Stored G H n (n + 1)
      ((List.range (n + 1)).foldl (fun p j => next G H leftSeed leftTime rightSeed rightTime n j p)
        (none, bits)).1
      ((List.range (n + 1)).foldl (fun p j => next G H leftSeed leftTime rightSeed rightTime n j p)
        (none, bits)).2 endStore := by
    simpa only [List.range_eq_range', Nat.zero_add] using last
  have eval_eq : (body G H leftSeed leftTime rightSeed rightTime).eval start =
      (WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide) id).eval endStore := by
    change (WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide) id).eval
      ((WordStack.Routine.counted 30 (splitStep G H leftSeed leftTime rightSeed rightTime)).eval^[(ready 30).length] ready) = _
    rw [clock]
  rw [eval_eq]
  constructor
  · simpa [WordStack.Routine.assign_eval] using result.master
  · simpa [WordStack.Routine.assign_eval, algorithm] using result.candidateWord
  · simpa [WordStack.Routine.assign_eval, algorithm] using result.found

end ComplexityOfGenerators.Simulation.ConcatenationGenerator
