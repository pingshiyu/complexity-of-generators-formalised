import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Weighted

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

private def reverseValue (i : ℕ) (left right : List α) (bits : BitString) : Option (List α) :=
  if right.length < i ∧ i < left.length then
    (RationalSelection.choose (left.length - right.length) (left.length - i) bits).map
      (fun choice => if choice then right else left)
  else none

private def strictValue (i : ℕ) (left right : List α) (bits : BitString) : Option (List α) :=
  if left.length < i ∧ i < right.length then
    (RationalSelection.choose (right.length - left.length) (right.length - i) bits).map
      (fun choice => if choice then left else right)
  else reverseValue i left right bits

theorem both_flags (first second : Fin 35) (yes no : Controller G) (s : Store G)
    (p q : Prop) [Decidable p] [Decidable q]
    (left : s first = if p then [Symbol.unit] else [])
    (right : s second = if q then [Symbol.unit] else []) :
    (both G first second yes no).eval s = (if p ∧ q then yes else no).eval s := by
  rw [both_eval]
  by_cases hp : p <;> by_cases hq : q <;> simp [left, right, hp, hq]

private theorem reverseCase_value (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s)
    (enough : Nat.clog 2 (left.length - right.length) ≤ bits.length) :
    Chosen G (reverseValue i left right bits) ((reverseCase G).eval s) := by
  let ready := (leftAbove G).eval ((rightBelow G).eval s)
  have tested := reverseTests G i left right bits s stored
  have branch := both_flags G 23 24 (weightedRight G) WordStack.Routine.skip ready
    (right.length < i) (i < left.length) tested.2.1 tested.2.2
  change Chosen G (reverseValue i left right bits)
    ((both G 23 24 (weightedRight G) WordStack.Routine.skip).eval ready)
  rw [branch]
  by_cases gate : right.length < i ∧ i < left.length
  · simp only [reverseValue, gate, ite_true]
    exact weightedRight_value G i left right bits ready tested.1 enough
  · simp only [reverseValue, gate, ite_false]
    exact ⟨tested.1.word, tested.1.found⟩

private theorem strictCases_value (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s)
    (enoughLeft : Nat.clog 2 (right.length - left.length) ≤ bits.length)
    (enoughRight : Nat.clog 2 (left.length - right.length) ≤ bits.length) :
    Chosen G (strictValue i left right bits) ((strictCases G).eval s) := by
  let ready := (rightAbove G).eval ((leftBelow G).eval s)
  have tested := forwardTests G i left right bits s stored
  have branch := both_flags G 23 24 (weightedLeft G) (reverseCase G) ready
    (left.length < i) (i < right.length) tested.2.1 tested.2.2
  change Chosen G (strictValue i left right bits)
    ((both G 23 24 (weightedLeft G) (reverseCase G)).eval ready)
  rw [branch]
  by_cases gate : left.length < i ∧ i < right.length
  · simp only [strictValue, gate, ite_true]
    exact weightedLeft_value G i left right bits ready tested.1 enoughLeft
  · simp only [strictValue, gate, ite_false]
    exact reverseCase_value G i left right bits ready tested.1 enoughRight

theorem equalCase_value (i : ℕ) (left right : List α) (bits : BitString) (s : Store G)
    (stored : PairStored G i left right bits s)
    (enoughLeft : Nat.clog 2 (right.length - left.length) ≤ bits.length)
    (enoughRight : Nat.clog 2 (left.length - right.length) ≤ bits.length) :
    Chosen G (BalancedPairPhase.balance i (some left) (some right) bits) ((equalCase G).eval s) := by
  let ready := (equalRight G).eval ((equalLeft G).eval s)
  have tested := equalTests G i left right bits s stored
  have branch := both_flags G 23 24 (pick G 25 (by decide)) (strictCases G) ready
    (left.length = i) (right.length = i) tested.2.1 tested.2.2
  change Chosen G (BalancedPairPhase.balance i (some left) (some right) bits)
    ((both G 23 24 (pick G 25 (by decide)) (strictCases G)).eval ready)
  rw [branch]
  by_cases gate : left.length = i ∧ right.length = i
  · simp only [BalancedPairPhase.balance, gate, ite_true]
    constructor
    · simpa [pick_eval, UnionGenerator.held] using tested.1.leftWord
    · simp [pick_eval, UnionGenerator.flagWord]
  · simp only [gate, ite_false]
    simpa only [BalancedPairPhase.balance, gate, ite_false, strictValue, reverseValue] using
      strictCases_value G i left right bits ready tested.1 enoughLeft enoughRight

structure Ready (i : ℕ) (first second : Option (List α)) (bits : BitString) (s : Store G) : Prop where
  target : (s 22).length = i
  leftWord : s 25 = UnionGenerator.held G G first
  leftFlag : s 27 = UnionGenerator.flagWord G G first.isSome
  rightWord : s 26 = UnionGenerator.held G G second
  rightFlag : s 28 = UnionGenerator.flagWord G G second.isSome
  random : s 17 = bits.map Symbol.bit
  word : s 31 = []
  found : s 32 = []

theorem classify_value (i : ℕ) (first second : Option (List α)) (bits : BitString) (s : Store G)
    (stored : Ready G i first second bits s)
    (enough : ∀ left right, first = some left → second = some right →
      Nat.clog 2 (right.length - left.length) ≤ bits.length ∧
      Nat.clog 2 (left.length - right.length) ≤ bits.length) :
    Chosen G (BalancedPairPhase.balance i first second bits) ((classify G).eval s) := by
  cases first with
  | none =>
    have unchanged : (classify G).eval s = s := by
      simp [classify, both, WordStack.Routine.branch, stored.leftFlag, UnionGenerator.flagWord,
        WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]
    rw [unchanged]
    cases second <;> exact ⟨stored.word, stored.found⟩
  | some left =>
    cases second with
    | none =>
      have unchanged : (classify G).eval s = s := by
        simp [classify, both, WordStack.Routine.branch, stored.leftFlag, stored.rightFlag,
          UnionGenerator.flagWord, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]
      rw [unchanged]
      exact ⟨stored.word, stored.found⟩
    | some right =>
      have pair : PairStored G i left right bits s :=
        ⟨stored.target, stored.leftWord, stored.rightWord, stored.random, stored.word, stored.found⟩
      have reduced : (classify G).eval s = (equalCase G).eval s := by
        simp [classify, both, WordStack.Routine.branch, stored.leftFlag, stored.rightFlag, UnionGenerator.flagWord]
      rw [reduced]
      exact equalCase_value G i left right bits s pair (enough left right rfl rfl).1 (enough left right rfl rfl).2

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
