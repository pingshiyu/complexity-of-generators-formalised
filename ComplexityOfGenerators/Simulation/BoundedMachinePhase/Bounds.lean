import ComplexityOfGenerators.Simulation.BoundedMachinePhase.Basic
import ComplexityOfGenerators.Simulation.UnionGenerator.Bounds

namespace ComplexityOfGenerators.Simulation.BoundedMachinePhase

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

theorem prepare_bound (s : Store M) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((prepare M).eval s) cap ∧ (prepare M).cost s ≤ 40 * (cap + 1) := by
  let a := (WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide)
    (fun _ => (Symbol.unit : Cell M))).eval s
  have aSize := sizes.assign (O := α) 22 13 33 (by decide) (by decide) (by decide) (fun _ => (Symbol.unit : Cell M))
  constructor
  · intro j
    change ((WordStack.Routine.clearMany (O := α) [11, 12, 14, 31, 32]).eval a j).length ≤ cap
    rw [WordStack.Routine.clearMany_eval]
    change (if j ∈ [11, 12, 14, 31, 32] then [] else a j).length ≤ cap
    split
    · simp
    · exact aSize j
  · have clearCost := WordStack.Routine.clearMany_cost (O := α)
      ([11, 12, 14, 31, 32] : List (Fin 35)) a cap (by intro j _; exact aSize j)
    have h13 := sizes 13
    have h22 := sizes 22
    have h33 := sizes 33
    change (WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide)
      (fun _ => (Symbol.unit : Cell M))).cost s + 1 +
      (WordStack.Routine.clearMany (O := α) [11, 12, 14, 31, 32]).cost a ≤ _
    simp only [WordStack.Routine.assign_cost, List.length_cons, List.length_nil] at *
    omega

theorem finish_bound (s : Store M) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((finish M).eval s) cap ∧ (finish M).cost s ≤ 13 * cap + 6 := by
  unfold finish
  simp only [WordStack.Routine.branch]
  split
  · obtain ⟨taken, takenCost⟩ := UnionGenerator.takeOutput_bound M M 31 (by decide) (UnionGenerator.leftOutput M M) s cap sizes
    obtain ⟨flagged, flagCost⟩ := UnionGenerator.flag_bound M M 32 true _ cap taken positive
    exact ⟨flagged, by simp only [WordStack.Routine.seq]; omega⟩
  · obtain ⟨flagged, flagCost⟩ := UnionGenerator.flag_bound M M 32 false _ cap (sizes.clear 31) positive
    exact ⟨flagged, by simp only [WordStack.Routine.seq, WordStack.Routine.clear]; have := sizes 31; omega⟩

noncomputable def cap (seed clock : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (100 * (Polynomial.X + 1 + seed.asPolynomial + 3 * clock.asPolynomial))

theorem cap_lower (seed clock : PolynomialBound) (n : ℕ) :
    100 * (n + 1 + seed n + 3 * clock n) ≤ cap seed clock n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (100 * (Polynomial.X + 1 + seed.asPolynomial + 3 * clock.asPolynomial)) n
  simpa only [cap, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_ofNat, PolynomialBound.asPolynomial_eval] using bound

noncomputable def time (seed clock : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (Polynomial.C ((Source.body M (Symbol.left : Source.Symbol M → Cell M) (UnionGenerator.leftDecode M M)
      (Source.bank BoundedSource.sourceSlots)).bound + 1000) * ((cap seed clock).asPolynomial + 1) +
      (Command.counterBudget seed).asPolynomial + (Command.counterBudget clock).asPolynomial)

theorem time_lower (seed clock : PolynomialBound) (n : ℕ) :
    ((Source.body M (Symbol.left : Source.Symbol M → Cell M) (UnionGenerator.leftDecode M M)
      (Source.bank BoundedSource.sourceSlots)).bound + 1000) * (cap seed clock n + 1) +
      Command.counterBudget seed n + Command.counterBudget clock n ≤ time M seed clock n := by
  exact (by
    simpa only [time, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_ofNat, PolynomialBound.asPolynomial_eval] using PolynomialBound.eval_le_ofPolynomial
      (Polynomial.C ((Source.body M (Symbol.left : Source.Symbol M → Cell M) (UnionGenerator.leftDecode M M)
        (Source.bank BoundedSource.sourceSlots)).bound + 1000) * ((cap seed clock).asPolynomial + 1) +
        (Command.counterBudget seed).asPolynomial + (Command.counterBudget clock).asPolynomial) n)

theorem phase_bound (seed clock : PolynomialBound) :
    FixedBlockRetry.PhaseBound Symbol.bit seed (cap seed clock) (time M seed clock) (phase M seed clock) := by
  intro n block s length _ master random sizes
  let r := (prepare M).eval s
  have lower := cap_lower seed clock n
  obtain ⟨rSize, rCost⟩ := prepare_bound M s _ sizes
  have ri : r 11 = [] := by simp [r, prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]
  have ra : r 12 = [] := by simp [r, prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]
  have re : r 14 = [] := by simp [r, prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]
  have rn : (r 13).length = n := by simpa [r, prepare, WordStack.Routine.seq,
    WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval] using master
  have rr : r 17 = block.map Symbol.bit := by simpa [r, prepare, WordStack.Routine.seq,
    WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval] using random
  obtain ⟨sourceSize, _, sourceCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) Symbol.unit Symbol.bit M Symbol.left (UnionGenerator.leftDecode M M)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit M M) (fun _ => rfl)
      seed clock r (generatorData n) block
      (by simp [ri, generatorData]) (by simp [ra, generatorData]) rn rr re _ rSize
      (by simpa [generatorData] using (by omega : n + 1 ≤ cap seed clock n))
      (by simpa [generatorData] using (by omega : seed n ≤ cap seed clock n))
      (by simpa [generatorData] using (by omega : clock n + 1 ≤ cap seed clock n))
      (by simpa [generatorData] using (by omega : 1 + n + seed n + 3 * (clock n + 1) ≤ cap seed clock n))
  obtain ⟨finalSize, finalCost⟩ := finish_bound M _ _ sourceSize (by omega)
  refine ⟨finalSize, ?_⟩
  apply le_trans _ (time_lower M seed clock n)
  change (UnionGenerator.leftTrial M M seed clock).cost r ≤ _ at sourceCost
  change (finish M).cost ((UnionGenerator.leftTrial M M seed clock).eval r) ≤ _ at finalCost
  change (prepare M).cost s + 1 + ((UnionGenerator.leftTrial M M seed clock).cost r + 1 +
    (finish M).cost ((UnionGenerator.leftTrial M M seed clock).eval r)) ≤ _
  simp only [generatorData, Nat.add_mul, Nat.mul_add] at sourceCost ⊢
  omega

theorem indexBudget (seed clock : PolynomialBound) (n : ℕ) : n + 1 ≤ cap seed clock n := by
  have := cap_lower seed clock n
  omega

theorem widthBudget (seed clock : PolynomialBound) (n : ℕ) : seed n ≤ cap seed clock n := by
  have := cap_lower seed clock n
  omega

end ComplexityOfGenerators.Simulation.BoundedMachinePhase
