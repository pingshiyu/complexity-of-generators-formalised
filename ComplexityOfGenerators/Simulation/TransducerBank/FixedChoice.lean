import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import ComplexityOfGenerators.Simulation.TransducerBank.RandomTape

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem RegionSteps.change_bits_interval {data : InputData I A} {bits : BitString} {radius time : ℕ}
    {start finish : BankConfiguration O Q S k} (path : B.RegionSteps data bits radius start time finish)
    (other : BitString) (same : ∀ index,start.randomHead ≤ index → index<finish.randomHead → bits[index]?=other[index]?) :
    B.RegionSteps data other radius start time finish := by
  induction path with
  | refl start bounded => exact .refl _ bounded
  | step start next write work input auxiliary index emit time finish bounded table rest ih =>
      exact .step start next write work input auxiliary index emit time finish bounded table (ih same)
  | random start no yes bit time finish bounded table lookup rest ih =>
      have increased := (rest.toSteps B).random_monotone B
      change start.randomHead+1≤finish.randomHead at increased
      have lookup' : other[start.randomHead]?=some bit :=
        (same start.randomHead le_rfl (by omega)).symm.trans lookup
      apply RegionSteps.random start no yes bit time finish bounded table lookup'
      apply ih
      intro index lower upper
      exact same index (by change start.randomHead+1 ≤ index at lower;omega) upper

/-- A deterministic finite transition table follows the same work path on
every choice tape, with exactly the same clock and terminal configuration. -/
theorem RegionSteps.change_bits (deterministic : B.Deterministic) {data : InputData I A}
    {bits : BitString} {radius time : ℕ} {start finish : BankConfiguration O Q S k}
    (path : B.RegionSteps data bits radius start time finish) (other : BitString) :
    B.RegionSteps data other radius start time finish := by
  induction path with
  | refl start bounded => exact .refl _ bounded
  | random start no yes bit time finish bounded table lookup rest ih =>
      have never := deterministic start.state data.input[start.inputHead]? data.auxiliary[start.auxiliaryHead]?
        (if start.indexHead<data.index then some () else none)
        (decide (start.head (B.select start.state)=0)) (start.tape (B.select start.state) (start.head (B.select start.state)))
      change match B.instruction data start with | .readRandom _ _ => False | _ => True at never
      simp [table] at never
  | step start next write work input auxiliary index emit time finish bounded table rest ih =>
      exact .step start next write work input auxiliary index emit time finish bounded table ih

theorem RegionRun.change_bits (deterministic : B.Deterministic) {data : InputData I A}
    {bits : BitString} {radius : ℕ} {start : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.RegionRun data bits radius start result) (other : BitString) :
    B.RegionRun data other radius start result := by
  obtain ⟨time,finish,path,terminal⟩ := run
  exact ⟨time,finish,path.change_bits B deterministic other,terminal.change_bits B deterministic other⟩

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
