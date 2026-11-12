import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- Every written work symbol lies within the bounded region. -/
def TapeSupported (radius : ℕ) (c : BankConfiguration O Q S k) : Prop :=
  ∀ j position, radius<position.natAbs → c.tape j position=B.blank

theorem initial_tapeSupported (radius : ℕ) : B.TapeSupported radius B.initialConfiguration := by
  intro j position outside
  rfl

theorem advance_tapeSupported (data : InputData I A) (radius : ℕ)
    (c : BankConfiguration O Q S k) (bounded : B.Bounded data radius c) (supported : B.TapeSupported radius c)
    (next write work input auxiliary index emit) :
    B.TapeSupported radius (B.advance data c next write work input auxiliary index emit) := by
  intro j position outside
  simp only [advance]
  by_cases selected : j=B.select c.state
  · subst j
    rw [Function.update_self]
    have different : position≠c.head (B.select c.state) := by
      intro equal
      have head:=bounded.head (B.select c.state)
      rw [equal] at outside
      omega
    rw [Function.update_of_ne different]
    exact supported _ _ outside
  · rw [Function.update_of_ne selected]
    exact supported _ _ outside

theorem RegionSteps.tapeSupported {data : InputData I A} {bits : BitString} {radius ticks : ℕ}
    {start finish : BankConfiguration O Q S k} (path : B.RegionSteps data bits radius start ticks finish)
    (supported : B.TapeSupported radius start) : B.TapeSupported radius finish := by
  induction path with
  | refl start bounded => exact supported
  | random start no yes bit ticks finish bounded table lookup rest ih => exact ih supported
  | step start next write work input auxiliary index emit ticks finish bounded table rest ih =>
    exact ih (B.advance_tapeSupported data radius start bounded supported next write work input auxiliary index emit)

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
