import ComplexityOfGenerators.Simulation.UnionGenerator.Components

set_option maxHeartbeats 800000

namespace ComplexityOfGenerators.Simulation.UnionGenerator

open WordStack

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

theorem sourceValue_eq_some (M : Machine Unit Bool α) (time : PolynomialBound)
    (n : ℕ) (bits : BitString) (word : List α) :
    sourceValue M time n bits = some word ↔
      M.run (generatorData n) bits (time n) = .halted (.accepted word) := by
  unfold sourceValue
  cases M.run (generatorData n) bits (time n) with
  | running c => simp [RunState.acceptedWord]
  | halted outcome => cases outcome <;> simp [RunState.acceptedWord, Outcome.acceptedWord]

theorem takeOutput_eval (dst : Fin 35) (different : (10 : Fin 35) ≠ dst)
    (map : Cell G H → Cell G H) (s : Store G H) :
    (takeOutput G H dst different map).eval s =
      Function.update (Function.update s 10 []) dst ((s 10).reverse.map map) := by
  funext j
  by_cases hd : j = dst <;> by_cases ho : j = 10 <;>
    simp_all [takeOutput, WordStack.Routine.seq, WordStack.Routine.clear,
      WordStack.Routine.transfer, Function.update_apply, different.symm]

theorem flag_eval (reg : Fin 35) (value : Bool) (s : Store G H) :
    (flag G H reg value).eval s = Function.update s reg (flagWord G H value) := by
  cases value <;> simp [flag, WordStack.Routine.seq, WordStack.Routine.clear,
    WordStack.Routine.ofLocal, WordStack.Routine.skip, Local.eval, Local.push,
    Action.apply, flagWord, Function.update_idem]

/-- A summary retaining both successful source results, including successful
empty output words, which have a separate status flag. -/
structure Stored (n : ℕ) (bits : BitString) (left right : Option (List α)) (s : Store G H) : Prop where
  input : s 11 = []
  auxiliary : s 12 = []
  index : (s 13).length = n
  random : s 17 = bits.map Symbol.bit
  empty : s 14 = []
  leftWord : s 25 = held G H left
  leftFlag : s 27 = flagWord G H left.isSome
  rightWord : s 26 = held G H right
  rightFlag : s 28 = flagWord G H right.isSome

theorem leftStep_stored (seed time : PolynomialBound) (n : ℕ) (bits : BitString)
    (left right : Option (List α)) (s : Store G H) (stored : Stored G H n bits left right s) :
    Stored G H n (bits.drop (seed n))
      (sourceValue G time n (bits.take (seed n))) right
      ((leftFinish G H).eval ((leftTrial G H seed time).eval s)) := by
  obtain ⟨status, output, state, result, native⟩ :=
    BoundedSource.sourceTrial_result (O := α) Symbol.unit Symbol.bit G Symbol.left (leftDecode G H)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (leftBit G H) (fun _ => rfl)
      seed time s (generatorData n) bits
      (by simp [stored.input, generatorData]) (by simp [stored.auxiliary, generatorData])
      stored.index stored.random stored.empty
  let t := (leftTrial G H seed time).eval s
  have outside (j : Fin 35) (large : 11 ≤ j.val) (clock : j ≠ 16) :=
    BoundedSource.sourceTrial_outside (O := α) Symbol.unit Symbol.bit G Symbol.left (leftDecode G H)
      (fun _ => .left .unit) (fun _ => .left .unit) (leftBit G H) seed time s j large clock
  have ti : t 11 = [] := by simpa [t, leftTrial, BoundedSource.trialPrepared, stored.input] using outside 11 (by decide) (by decide)
  have ta : t 12 = [] := by simpa [t, leftTrial, BoundedSource.trialPrepared, stored.auxiliary] using outside 12 (by decide) (by decide)
  have tn : (t 13).length = n := by
    simpa [t, leftTrial, BoundedSource.trialPrepared, stored.index] using congrArg List.length (outside 13 (by decide) (by decide))
  have tr : t 17 = (bits.drop (seed n)).map Symbol.bit := by
    simpa [t, leftTrial, BoundedSource.trialPrepared, stored.random, stored.index, List.map_drop] using outside 17 (by decide) (by decide)
  have te : t 14 = [] := by simpa [t, leftTrial] using outside 14 (by decide) (by decide)
  have tw : t 26 = held G H right := by simpa [t, leftTrial, BoundedSource.trialPrepared, stored.rightWord] using outside 26 (by decide) (by decide)
  have tf : t 28 = flagWord G H right.isSome := by simpa [t, leftTrial, BoundedSource.trialPrepared, stored.rightFlag] using outside 28 (by decide) (by decide)
  change ∀ word, (status = .accepted ∧ output.reverse = word) ↔
    G.run (generatorData n) (bits.take (seed n)) (time n) = .halted (.accepted word) at native
  have val : sourceValue G time n (bits.take (seed n)) =
      (if status = .accepted then some output.reverse else none) := by
    apply Option.ext
    intro word
    rw [sourceValue_eq_some, ← native]
    by_cases h : status = .accepted <;> simp [h]
  change t 0 = [.left (.state status)] at state
  change t 10 = output.map (fun a => Symbol.left (Source.Cell.output a)) at result
  change Stored G H n _ _ _ ((leftFinish G H).eval t)
  rw [val]
  cases status <;>
    constructor <;>
    simp_all [leftFinish, WordStack.Routine.branch, WordStack.Routine.seq,
      takeOutput_eval, flag_eval, WordStack.Routine.clear, flagWord, held, letters, leftOutput,
      List.map_map, Function.comp_def, List.map_reverse]

theorem rightStep_stored (seed time : PolynomialBound) (n : ℕ) (bits : BitString)
    (left right : Option (List α)) (s : Store G H) (stored : Stored G H n bits left right s) :
    Stored G H n (bits.drop (seed n)) left
      (sourceValue H time n (bits.take (seed n)))
      ((rightFinish G H).eval ((rightTrial G H seed time).eval s)) := by
  obtain ⟨status, output, state, result, native⟩ :=
    BoundedSource.sourceTrial_result (O := α) Symbol.unit Symbol.bit H Symbol.right (rightDecode G H)
      (fun _ => rfl) (fun _ => .right .unit) (fun _ => .right .unit) (rightBit G H) (fun _ => rfl)
      seed time s (generatorData n) bits
      (by simp [stored.input, generatorData]) (by simp [stored.auxiliary, generatorData])
      stored.index stored.random stored.empty
  let t := (rightTrial G H seed time).eval s
  have outside (j : Fin 35) (large : 11 ≤ j.val) (clock : j ≠ 16) :=
    BoundedSource.sourceTrial_outside (O := α) Symbol.unit Symbol.bit H Symbol.right (rightDecode G H)
      (fun _ => .right .unit) (fun _ => .right .unit) (rightBit G H) seed time s j large clock
  have ti : t 11 = [] := by simpa [t, rightTrial, BoundedSource.trialPrepared, stored.input] using outside 11 (by decide) (by decide)
  have ta : t 12 = [] := by simpa [t, rightTrial, BoundedSource.trialPrepared, stored.auxiliary] using outside 12 (by decide) (by decide)
  have tn : (t 13).length = n := by
    simpa [t, rightTrial, BoundedSource.trialPrepared, stored.index] using congrArg List.length (outside 13 (by decide) (by decide))
  have tr : t 17 = (bits.drop (seed n)).map Symbol.bit := by
    simpa [t, rightTrial, BoundedSource.trialPrepared, stored.random, stored.index, List.map_drop] using outside 17 (by decide) (by decide)
  have te : t 14 = [] := by simpa [t, rightTrial] using outside 14 (by decide) (by decide)
  have tw : t 25 = held G H left := by simpa [t, rightTrial, BoundedSource.trialPrepared, stored.leftWord] using outside 25 (by decide) (by decide)
  have tf : t 27 = flagWord G H left.isSome := by simpa [t, rightTrial, BoundedSource.trialPrepared, stored.leftFlag] using outside 27 (by decide) (by decide)
  change ∀ word, (status = .accepted ∧ output.reverse = word) ↔
    H.run (generatorData n) (bits.take (seed n)) (time n) = .halted (.accepted word) at native
  have val : sourceValue H time n (bits.take (seed n)) =
      (if status = .accepted then some output.reverse else none) := by
    apply Option.ext
    intro word
    rw [sourceValue_eq_some, ← native]
    by_cases h : status = .accepted <;> simp [h]
  change t 0 = [.right (.state status)] at state
  change t 10 = output.map (fun a => Symbol.right (Source.Cell.output a)) at result
  change Stored G H n _ _ _ ((rightFinish G H).eval t)
  rw [val]
  cases status <;>
    constructor <;>
    simp_all [rightFinish, WordStack.Routine.branch, WordStack.Routine.seq,
      takeOutput_eval, flag_eval, WordStack.Routine.clear, flagWord, held, letters, rightOutput,
      List.map_map, Function.comp_def, List.map_reverse]

/-- The final chosen word and its availability status. -/
structure Chosen (n : ℕ) (value : Option (List α)) (s : Store G H) : Prop where
  index : (s 13).length = n
  word : s 11 = held G H value
  available : s 29 = flagWord G H value.isSome

theorem choose_stored (n : ℕ) (bits : BitString) (left right : Option (List α))
    (s : Store G H) (stored : Stored G H n bits left right s) :
    Chosen G H n (if bits.head? = some true then right.or left else left.or right)
      ((choose G H).eval s) := by
  rcases stored with ⟨input, auxiliary, index, random, empty, lw, lf, rw, rf⟩
  cases bits with
  | nil =>
    cases left <;> cases right <;>
      constructor <;>
      simp [choose, chooseFrom, random, lw, lf, rw, rf, index, WordStack.Routine.branch, WordStack.Routine.seq,
        WordStack.Routine.assign_eval, WordStack.Routine.clear, flag_eval, flagWord, held,
        letters, Option.or]
  | cons bit rest =>
    cases bit <;> cases left <;> cases right <;>
      constructor <;>
      simp [choose, chooseFrom, random, lw, lf, rw, rf, index, WordStack.Routine.branch, WordStack.Routine.seq,
        WordStack.Routine.assign_eval, WordStack.Routine.clear, flag_eval, flagWord, held,
        letters, Option.or]

theorem body_chosen (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n read : ℕ) (bits : BitString) :
    Chosen G H n (value G H leftSeed leftTime rightSeed rightTime n bits)
      ((body G H leftSeed leftTime rightSeed rightTime).eval
        (BoundedSource.preparedMemory (O := α) Symbol.unit Symbol.bit n read bits).store) := by
  have initial : Stored G H n bits none none
      (BoundedSource.preparedMemory (O := α) Symbol.unit Symbol.bit n read bits).store := by
    constructor <;> simp [BoundedSource.preparedMemory, held, flagWord]
  have left := leftStep_stored G H leftSeed leftTime n bits none none _ initial
  have right := rightStep_stored G H rightSeed rightTime n (bits.drop (leftSeed n))
    (sourceValue G leftTime n (bits.take (leftSeed n))) none _ left
  have chosen := choose_stored G H n ((bits.drop (leftSeed n)).drop (rightSeed n))
    _ _ _ right
  simpa only [body, WordStack.Routine.seq, value, List.drop_drop] using chosen

end ComplexityOfGenerators.Simulation.UnionGenerator
