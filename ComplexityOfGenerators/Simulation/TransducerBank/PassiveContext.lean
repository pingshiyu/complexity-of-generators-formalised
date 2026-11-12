import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Context

/-! Frame rules for finite controllers that touch only their work tapes.
The hypotheses inspect the actual finite transition table. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank

set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ}

structure TapeBank.WorkOnly (B : TapeBank I A O Q S k) : Prop where
  independent : ∀ state input auxiliary index origin cell,
    B.transition state input auxiliary index origin cell=B.transition state none none none origin cell
  silent : ∀ state input auxiliary index origin cell,
    match B.transition state input auxiliary index origin cell with
    | .readRandom _ _ => False
    | .step _ _ _ i a x emit => i=.stay ∧ a=.stay ∧ x=.stay ∧ emit=none
    | _ => True

namespace BinaryCounter.Context

def frame (context : BinaryCounter.Context O) (configuration : BankConfiguration O Q S k) : BankConfiguration O Q S k :=
  {configuration with
    inputHead := context.inputHead
    auxiliaryHead := context.auxiliaryHead
    indexHead := context.indexHead
    randomHead := context.randomHead
    output := context.output}

theorem instruction_frame (B : TapeBank I A O Q S k) (workOnly : B.WorkOnly) (data : InputData I A)
    (context : BinaryCounter.Context O) (configuration : BankConfiguration O Q S k) :
    B.instruction data (frame context configuration)=B.instruction data configuration := by
  simp only [TapeBank.instruction,frame]
  rw [workOnly.independent,workOnly.independent configuration.state data.input[configuration.inputHead]?
    data.auxiliary[configuration.auxiliaryHead]?]

theorem advance_frame (B : TapeBank I A O Q S k) (data : InputData I A) (context : BinaryCounter.Context O)
    (valid : context.Valid data) (configuration : BankConfiguration O Q S k) (next write work) :
    B.advance data (frame context configuration) next write work .stay .stay .stay none=
      frame context (B.advance data configuration next write work .stay .stay .stay none) := by
  rcases valid with ⟨input,auxiliary,index⟩
  apply BankConfiguration.ext <;>
    simp [TapeBank.advance,frame,Move.onInput,Nat.min_eq_left input,Nat.min_eq_left auxiliary,Nat.min_eq_left index]

theorem frame_bounded (B : TapeBank I A O Q S k) (data : InputData I A) (context : BinaryCounter.Context O)
    (valid : context.Valid data) (radius : ℕ) (configuration : BankConfiguration O Q S k)
    (bounded : B.Bounded data radius configuration) : B.Bounded data radius (frame context configuration) :=
  ⟨valid.1,valid.2.1,valid.2.2,bounded.head⟩

theorem regionSteps_frame (B : TapeBank I A O Q S k) (workOnly : B.WorkOnly)
    (data : InputData I A) (choices : BitString) (context : BinaryCounter.Context O) (valid : context.Valid data)
    {radius time : ℕ} {source target : BankConfiguration O Q S k}
    (path : B.RegionSteps data choices radius source time target) :
    B.RegionSteps data choices radius (frame context source) time (frame context target) := by
  induction path with
  | refl source bounded => exact .refl _ (frame_bounded B data context valid radius source bounded)
  | random source no yes bit time target bounded table lookup rest ih =>
      have never := workOnly.silent source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
        (if source.indexHead<data.index then some () else none)
        (decide (source.head (B.select source.state)=0)) (source.tape (B.select source.state) (source.head (B.select source.state)))
      change match B.instruction data source with
        | .readRandom _ _ => False
        | .step _ _ _ i a x emit => i=.stay ∧ a=.stay ∧ x=.stay ∧ emit=none
        | _ => True at never
      simp [table] at never
  | step source next write work input auxiliary index emit time target bounded table rest ih =>
      have moves := workOnly.silent source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
        (if source.indexHead<data.index then some () else none)
        (decide (source.head (B.select source.state)=0)) (source.tape (B.select source.state) (source.head (B.select source.state)))
      change match B.instruction data source with
        | .readRandom _ _ => False
        | .step _ _ _ i a x emit => i=.stay ∧ a=.stay ∧ x=.stay ∧ emit=none
        | _ => True at moves
      rw [table] at moves
      obtain ⟨rfl,rfl,rfl,rfl⟩ := moves
      apply TapeBank.RegionSteps.step (frame context source) next write work .stay .stay .stay none time
        (frame context target) (frame_bounded B data context valid radius source bounded)
      · rw [instruction_frame B workOnly]
        exact table
      · rw [advance_frame B data context valid]
        exact ih

end BinaryCounter.Context
end ComplexityOfGenerators.Simulation.TransducerBank
