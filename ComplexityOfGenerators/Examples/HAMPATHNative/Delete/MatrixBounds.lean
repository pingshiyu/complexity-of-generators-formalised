import ComplexityOfGenerators.Examples.HAMPATHNative.Delete.Views
import ComplexityOfGenerators.Examples.HAMPATHNative.Delete.BasicBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Delete

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem matrixBase_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (matrixBase (O := O) s) (budget + 1) :=
  header_bound _ budget (sizes.assign 24 2 9 (by decide) (by decide) (by decide) id)

/-- Erasing the square matrix does not duplicate its consumed input. The
accumulator and unread suffix therefore share one linear store cap. -/
theorem matrixPair_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((MatrixErase.rows (O := O)).eval ((matrixPrepare (O := O)).eval s)) (2 * budget + 3) ∧
      (matrixPrepare (O := O)).cost s + 1 +
        (MatrixErase.rows (O := O)).cost ((matrixPrepare (O := O)).eval s) ≤ 1000 * (budget + 2)^2 := by
  let base := matrixBase (O := O) s
  let size := headerSize (s 24)
  let start := (s 26).length
  let initial : MatrixErase.State := ⟨(headerState (s 24)).word, start, true, s 29⟩
  let cap := 2 * budget + 2
  have baseBound : StoreBound base (budget + 1) := matrixBase_bound s budget sizes
  have sizeBound : size ≤ budget := (headerSize_le (s 24)).trans (sizes 24)
  have startBound : start ≤ budget := sizes 26
  have inputBound : initial.word.length ≤ budget := (headerState_word_le (s 24)).trans (sizes 24)
  have outputBound : initial.outRev.length ≤ budget := sizes 29
  have measure : initial.word.length + initial.outRev.length ≤ cap := by dsimp [cap]; omega
  have currentMeasure := MatrixErase.iterate_measure size start size initial
  have currentCounter := MatrixErase.iterate_countdown size start size initial
  have finalBound := MatrixErase.encoded_bound base size start ((MatrixErase.step size start)^[size] initial) [] cap
    (baseBound.mono (by dsimp [cap]; omega)) (by dsimp [cap]; omega) (by dsimp [cap]; omega)
    (by change ((MatrixErase.step size start)^[size] initial).countdown ≤ cap
        rw [currentCounter]
        change start - size ≤ cap
        dsimp [cap]
        omega)
    (by simp) (currentMeasure.trans measure)
  have rowsCost := MatrixErase.rows_cost (O := O) base size start initial size cap
    (baseBound.mono (by dsimp [cap]; omega)) (by dsimp [cap]; omega) (by dsimp [cap]; omega)
    (by change start ≤ cap; dsimp [cap]; omega) (by dsimp [cap]; omega) measure
  have prepCost := (matrixPrepare_bound (O := O) s budget sizes).2
  constructor
  · rw [matrixPrepare_eval, MatrixErase.rows_eval]
    simpa only [base, size, start, initial, cap, Nat.add_assoc] using finalBound
  · rw [matrixPrepare_eval]
    change (matrixPrepare (O := O)).cost s + 1 +
      (MatrixErase.rows (O := O)).cost (MatrixErase.encoded base size start initial (List.replicate size (.bit true))) ≤ _
    dsimp only [cap] at rowsCost
    nlinarith only [prepCost, rowsCost, sizeBound,
      Nat.mul_le_mul_right (200 * (2 * budget + 2 + 2)) sizeBound]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Delete
