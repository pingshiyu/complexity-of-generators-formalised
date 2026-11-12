import ComplexityOfGenerators.Examples.HAMPATHNative.RankBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.StateBounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineWordFunction

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def rankTime : PolynomialBound := PolynomialBound.ofPolynomial
  (4000 * (Polynomial.X + 2) * (((Polynomial.X + 1)^2 + 10 * (Polynomial.X + 2)) + 1)^2)

theorem rankRoutine_time (word : List Symbol) (auxiliary : List Unit) :
    rankRoutine.cost (loaded word auxiliary).store + 1 +
      4 * (rankRoutine.eval (loaded word auxiliary).store 20).length ≤
      rankTime (word.length + auxiliary.length) := by
  let n := word.length + auxiliary.length
  let s := (prepared word auxiliary).store
  have first : prepare.cost (loaded word auxiliary).store = 6 * word.length := by
    simp [prepare, loaded, Routine.transfer]
  have parseCost := parser_cost (O := Unit) s n (prepared_sizes word auxiliary)
  have parseBound : StoreBound ((parser (O := Unit)).eval s) (n + 1) := parser_bound s n (prepared_sizes word auxiliary)
  have last := rankCore_cost (O := Unit) ((parser (O := Unit)).eval s) (n + 1) (by omega) parseBound
  have output := word_rank_bound word
  rw [rankRoutine_value, List.length_replicate]
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_one]
  rw [show (n + 1)^2 + 10 * (n + 2) + 1 = rankWorkspace (n + 1) + 1 by
    simp only [rankWorkspace, pow_two, Nat.add_assoc]]
  change prepare.cost (loaded word auxiliary).store + 1 +
    ((parser (O := Unit)).cost s + 1 + (rankCore (O := Unit)).cost ((parser (O := Unit)).eval s)) + 1 +
      4 * wordRank word ≤ 4000 * (n + 2) * (rankWorkspace (n + 1) + 1)^2
  rw [first]
  have inside : word.length ≤ n := by dsimp [n]; omega
  have workspace : n + 1 ≤ rankWorkspace (n + 1) + 1 := by
    have bound := (rankWorkspace_large (n + 1)).1
    omega
  have square := Nat.pow_le_pow_left workspace 2
  have positive : 1 ≤ (rankWorkspace (n + 1) + 1)^2 := by
    nlinarith only [Nat.zero_le (rankWorkspace (n + 1))]
  have scalar : n + 1 ≤ (rankWorkspace (n + 1) + 1)^2 := by
    nlinarith only [workspace, Nat.zero_le (rankWorkspace (n + 1))]
  nlinarith only [parseCost, last, output, inside, square, positive, scalar,
    Nat.zero_le (n * (rankWorkspace (n + 1) + 1)^2)]

/-- The weighted self-reduction rank is computed by a finite native loop
that adds each successive binary label width. -/
noncomputable def rank_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => List.replicate (wordRank word) ()) := by
  apply Routine.polynomialWordFunction rankRoutine 0 1 0 20 (by decide) id
    (fun (_ : Unit) => Symbol.bit false) (fun _ => some ())
    (fun word _ => List.replicate (wordRank word) ()) rankTime rankRoutine_randomFree
  · intro word auxiliary
    have loadedEq : InputBank.loadedMemory (O := Unit) (0 : Fin 32) 1 (id : Symbol → Symbol)
        (fun (_ : Unit) => Symbol.bit false) ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) =
        loaded word auxiliary := by simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
    rw [loadedEq, rankRoutine_value]
    simp
  · intro word auxiliary
    have loadedEq : InputBank.loadedMemory (O := Unit) (0 : Fin 32) 1 (id : Symbol → Symbol)
        (fun (_ : Unit) => Symbol.bit false) ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) =
        loaded word auxiliary := by simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
    simpa only [loadedEq] using rankRoutine_time word auxiliary

end ComplexityOfGenerators.Examples.HAMPATH.Native
