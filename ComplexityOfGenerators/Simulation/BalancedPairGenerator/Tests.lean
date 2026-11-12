import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Components

set_option maxHeartbeats 1000000

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

structure Chosen (answer : Option (List α)) (s : Store G) : Prop where
  word : s 31 = UnionGenerator.held G G answer
  found : s 32 = UnionGenerator.flagWord G G answer.isSome

structure PairStored (i : ℕ) (left right : List α) (bits : BitString) (s : Store G) : Prop where
  target : (s 22).length = i
  leftWord : s 25 = UnionGenerator.letters G G left
  rightWord : s 26 = UnionGenerator.letters G G right
  random : s 17 = bits.map Symbol.bit
  word : s 31 = []
  found : s 32 = []

theorem both_eval (first second : Fin 35) (yes no : Controller G) (s : Store G) :
    (both G first second yes no).eval s =
      (if (s first).head?.isSome && (s second).head?.isSome then yes else no).eval s := by
  cases left : s first <;> cases right : s second <;>
    simp [both, WordStack.Routine.branch, left, right]

theorem equalTests (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s) :
    let result := (equalRight G).eval ((equalLeft G).eval s)
    PairStored G i left right bits result ∧
      result 23 = (if left.length = i then [Symbol.unit] else []) ∧
      result 24 = (if right.length = i then [Symbol.unit] else []) := by
  rcases stored with ⟨target, lw, rw, random, word, found⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor <;>
      simp [equalLeft, equalRight, LengthTest.routine_eval, target, lw, rw, random, word, found]
  · simp [equalLeft, equalRight, LengthTest.routine_eval, target, lw, UnionGenerator.letters]
  · simp [equalLeft, equalRight, LengthTest.routine_eval, target, rw, UnionGenerator.letters]

theorem forwardTests (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s) :
    let result := (rightAbove G).eval ((leftBelow G).eval s)
    PairStored G i left right bits result ∧
      result 23 = (if left.length < i then [Symbol.unit] else []) ∧
      result 24 = (if i < right.length then [Symbol.unit] else []) := by
  rcases stored with ⟨target, lw, rw, random, word, found⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor <;>
      simp [leftBelow, rightAbove, RationalSelection.Compare.routine_eval, target, lw, rw, random, word, found]
  · simp [leftBelow, rightAbove, RationalSelection.Compare.routine_eval, target, lw, UnionGenerator.letters]
  · simp [leftBelow, rightAbove, RationalSelection.Compare.routine_eval, target, rw, UnionGenerator.letters]

theorem reverseTests (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s) :
    let result := (leftAbove G).eval ((rightBelow G).eval s)
    PairStored G i left right bits result ∧
      result 23 = (if right.length < i then [Symbol.unit] else []) ∧
      result 24 = (if i < left.length then [Symbol.unit] else []) := by
  rcases stored with ⟨target, lw, rw, random, word, found⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor <;>
      simp [rightBelow, leftAbove, RationalSelection.Compare.routine_eval, target, lw, rw, random, word, found]
  · simp [rightBelow, leftAbove, RationalSelection.Compare.routine_eval, target, rw, UnionGenerator.letters]
  · simp [rightBelow, leftAbove, RationalSelection.Compare.routine_eval, target, lw, UnionGenerator.letters]

theorem selectionFinish_value (low high : Fin 35) (lowDifferent : low ≠ 31 ∧ low ≠ 33)
    (highDifferent : high ≠ 31 ∧ high ≠ 33) (lower upper : List α) (s : Store G)
    (lowWord : s low = UnionGenerator.letters G G lower)
    (highWord : s high = UnionGenerator.letters G G upper) (empty : s 31 = []) (failed : s 32 = []) :
    Chosen G ((PreparedRationalSelection.result s).map (fun choice => if choice then lower else upper))
      ((selectionFinish G low high lowDifferent highDifferent).eval s) := by
  cases valid : s 12 <;> cases choice : s 13 <;>
    constructor <;>
    simp [selectionFinish, PreparedRationalSelection.result, WordStack.Routine.branch, valid, choice,
      WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, pick_eval,
      lowWord, highWord, empty, failed, UnionGenerator.held, UnionGenerator.flagWord]

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
