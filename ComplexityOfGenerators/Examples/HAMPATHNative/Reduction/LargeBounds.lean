import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Components
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Bounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem edgeAndDelete_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((edgeAndDelete (O := O)).eval s) (8 * (budget + 4)) ∧
      (edgeAndDelete (O := O)).cost s ≤ 3000 * (budget + 5)^2 := by
  let q := (Edge.query (O := O)).eval s
  obtain ⟨qBound, qCost⟩ := Edge.query_bound (O := O) s budget sizes
  obtain ⟨deleteBound, deleteCost⟩ := Delete.routine_bound (O := O) q (budget + 1) qBound
  obtain ⟨finalBound, finalCost⟩ := Routine.guardedOutput_bound 16 31 (Delete.routine (O := O)) q
    (budget + 1) (8 * (budget + 1 + 3)) (2000 * (budget + 1 + 4)^2)
    qBound (by omega) deleteBound deleteCost
  refine ⟨finalBound.mono (by omega), ?_⟩
  change (Edge.query (O := O)).cost s + 1 + (afterEdge (O := O)).cost q ≤ _
  change (afterEdge (O := O)).cost q ≤ _ at finalCost
  nlinarith only [qCost, finalCost]

theorem afterLabel_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((afterLabel (O := O)).eval s) (8 * (budget + 4)) ∧
      (afterLabel (O := O)).cost s ≤ 3100 * (budget + 5)^2 := by
  obtain ⟨bodyBound, bodyCost⟩ := edgeAndDelete_bound (O := O) s budget sizes
  obtain ⟨finalBound, finalCost⟩ := Routine.guardedOutput_bound 16 31 (edgeAndDelete (O := O)) s
    budget (8 * (budget + 4)) (3000 * (budget + 5)^2) sizes (by omega) bodyBound bodyCost
  exact ⟨finalBound, by change (afterLabel (O := O)).cost s ≤ _ at finalCost; nlinarith only [finalCost]⟩

theorem pow_clog_bounded (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * (n + 1) := by
  by_cases zero : n = 0
  · simp [zero]
  · exact (RationalSelection.pow_clog_le_twice n (by omega)).trans (by omega)

theorem large_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((large (O := O)).eval s) (1000 * (budget + 2)) ∧
      (large (O := O)).cost s ≤ 10000000 * (budget + 2)^2 := by
  let capA := 4 * (budget + 1)
  let capB := 10 * (capA + 1)
  let a := (Logarithm.routine (O := O)).eval s
  let b := (LabelBits.routine (O := O)).eval a
  let c := (LabelChecks.routine (O := O)).eval b
  obtain ⟨aBound, aCost⟩ := Logarithm.routine_bound (O := O) s budget sizes
  change StoreBound a capA at aBound
  have width : (a 19).length = Nat.clog 2 (s 17).length := by
    simpa only [a, List.length_replicate] using congrArg List.length (Logarithm.routine_value (O := O) s)
  have range : 2 ^ (a 19).length ≤ capA := by
    rw [width]
    have power := pow_clog_bounded (s 17).length
    have source := sizes 17
    dsimp only [capA]
    omega
  obtain ⟨bBound, bCost⟩ := LabelBits.routine_bound (O := O) a capA aBound range
  change StoreBound b capB at bBound
  obtain ⟨cBound, cCost⟩ := LabelChecks.routine_bound (O := O) b capB (by dsimp [capB, capA]; omega) bBound
  change StoreBound c capB at cBound
  obtain ⟨finalBound, finalCost⟩ := afterLabel_bound (O := O) c capB cBound
  constructor
  · change StoreBound ((afterLabel (O := O)).eval c) _
    exact finalBound.mono (by dsimp [capB, capA]; omega)
  · change (Logarithm.routine (O := O)).cost s + 1 +
      ((LabelBits.routine (O := O)).cost a + 1 +
        ((LabelChecks.routine (O := O)).cost b + 1 + (afterLabel (O := O)).cost c)) ≤ _
    dsimp only [capB, capA] at bCost cCost finalCost
    nlinarith only [aCost, bCost, cCost, finalCost]

theorem large_randomFree {O : Type} : Command.RandomFree (large (O := O)).command := by
  have deleted : Command.RandomFree (afterEdge (O := O)).command :=
    Routine.guardedOutput_randomFree 16 31 _ Delete.routine_randomFree
  have checked : Command.RandomFree (edgeAndDelete (O := O)).command := .seq Edge.query_randomFree deleted
  have guarded : Command.RandomFree (afterLabel (O := O)).command :=
    Routine.guardedOutput_randomFree 16 31 _ checked
  exact .seq Logarithm.routine_randomFree (.seq LabelBits.routine_randomFree (.seq LabelChecks.routine_randomFree guarded))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
