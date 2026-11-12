import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Classify
import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Calls
import ComplexityOfGenerators.Simulation.BalancedPairGenerator.ClassifyBounds
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Components
import ComplexityOfGenerators.Foundations.BalancedPairProbability

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem phase_chosen (seed time bound : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store G)
    (index : (s 13).length = n) (master : (s 22).length = n) (random : s 17 = bits.map Symbol.bit)
    (enough : 2 * seed n + bound n ≤ bits.length)
    (short : ∀ block word, BalancedPairPhase.cappedCall G n (time n) block = some word → word.length ≤ bound n) :
    Chosen G (BalancedPairPhase.value G n (time n) (seed n) (bound n) bits) ((phase G seed time).eval s) := by
  let first := UnionGenerator.sourceValue G time n (bits.take (seed n))
  let second := UnionGenerator.sourceValue G time n ((bits.drop (seed n)).take (seed n))
  let tail := bits.drop (2 * seed n)
  let r := (calls G seed time).eval s
  have source := calls_stored G seed time n bits s index random
  have target : (r 22).length = n :=
    (congrArg List.length (calls_fixes22 G seed time s)).trans master
  have empty : r 31 = [] := by simpa using calls_outer G seed time s 31 (Or.inr (Or.inl rfl))
  have failed : r 32 = [] := by simpa using calls_outer G seed time s 32 (Or.inr (Or.inr rfl))
  have ready : Ready G n first second tail r :=
    ⟨target, source.leftWord, source.leftFlag, source.rightWord, source.rightFlag, source.random, empty, failed⟩
  have firstBound : ∀ word, first = some word → word.length ≤ bound n := by
    intro word output
    exact short _ word output
  have secondBound : ∀ word, second = some word → word.length ≤ bound n := by
    intro word output
    exact short _ word output
  have selectorBudget : bound n ≤ tail.length := by
    simp only [tail, List.length_drop]
    omega
  have answer := classify_value G n first second tail r ready (by
    intro left right leftOutput rightOutput
    have leftLength := firstBound left leftOutput
    have rightLength := secondBound right rightOutput
    have leftLog : Nat.clog 2 (right.length - left.length) ≤ bound n :=
      (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
    have rightLog : Nat.clog 2 (left.length - right.length) ≤ bound n :=
      (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
    exact ⟨leftLog.trans selectorBudget, rightLog.trans selectorBudget⟩)
  have value_eq : BalancedPairPhase.value G n (time n) (seed n) (bound n) bits =
      BalancedPairPhase.balance n first second tail :=
    BalancedPairPhase.balance_take_eq n (bound n) first second tail firstBound secondBound
  rw [value_eq]
  exact answer

theorem phase_correct (seed time width bound : PolynomialBound)
    (enough : ∀ n, 2 * seed n + bound n ≤ width n)
    (short : ∀ n block word, BalancedPairPhase.cappedCall G n (time n) block = some word → word.length ≤ bound n) :
    FixedBlockRetry.PhaseCorrect (Symbol.unit : Cell G) Symbol.bit (UnionGenerator.outputLetter G G)
      width (phase G seed time) (fun n bits => BalancedPairPhase.value G n (time n) (seed n) (bound n) bits) := by
  intro n block s length index master random
  have answer := phase_chosen G seed time bound n block s index master random (by rw [length]; exact enough n) (short n)
  refine ⟨answer.found, ?_⟩
  intro word output
  have payload := answer.word
  change BalancedPairPhase.value G n (time n) (seed n) (bound n) block = some word at output
  rw [output] at payload
  rw [payload]
  simp [UnionGenerator.held, UnionGenerator.letters, List.filterMap_map, Function.comp_def, UnionGenerator.outputLetter]

theorem phase_fixes22 (seed time : PolynomialBound) : (phase G seed time).Fixes 22 :=
  (calls_fixes22 G seed time).seq (classify_fixes22 G)

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
