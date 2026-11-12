import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! A finite scan to the end of the ordinary input. It needs no work-space
counter and changes no work cell, other readonly head, output, or random head. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.InputEnd

set_option backward.isDefEq.respectTransparency false

def bank (I A O S : Type) {k : ℕ} (blank : S) (selected : Fin k) : TapeBank I A O Unit S k where
  initial := ()
  blank := blank
  select := fun _ => selected
  transition := fun state input _ _ _ cell =>
    if input.isSome then .step state cell .stay .right .stay .stay none else .accept

theorem advance_right {I A O S : Type} {k : ℕ} (blank : S) (selected : Fin k) (data : InputData I A)
    (configuration : BankConfiguration O Unit S k) (radius : ℕ)
    (bounded : (bank I A O S blank selected).Bounded data radius configuration) :
    (bank I A O S blank selected).advance data configuration configuration.state
      (configuration.tape selected (configuration.head selected)) .stay .right .stay .stay none=
      {configuration with inputHead := min (configuration.inputHead+1) data.input.length} := by
  apply BankConfiguration.ext <;> try rfl
  all_goals simp [TapeBank.advance,bank,Move.onInput,Move.onInt,Nat.min_eq_left bounded.auxiliary,
    Nat.min_eq_left bounded.index,Function.update_eq_self]

theorem scan_regionSteps {I A O S : Type} {k : ℕ} (blank : S) (selected : Fin k) (data : InputData I A)
    (choices : BitString) (radius : ℕ) (configuration : BankConfiguration O Unit S k)
    (bounded : (bank I A O S blank selected).Bounded data radius configuration) (remaining : ℕ)
    (distance : configuration.inputHead+remaining=data.input.length) :
    (bank I A O S blank selected).RegionSteps data choices radius configuration remaining
      {configuration with inputHead := data.input.length} := by
  induction remaining generalizing configuration with
  | zero =>
      have endHead : configuration.inputHead=data.input.length := by omega
      rw [← endHead]
      exact .refl _ bounded
  | succ remaining ih =>
      have present : configuration.inputHead<data.input.length := by omega
      have table : (bank I A O S blank selected).instruction data configuration=
          .step configuration.state (configuration.tape selected (configuration.head selected)) .stay .right .stay .stay none := by
        simp [TapeBank.instruction,bank,List.getElem?_eq_getElem present]
      apply TapeBank.RegionSteps.step configuration configuration.state _ .stay .right .stay .stay none remaining _ bounded table
      rw [advance_right blank selected data configuration radius bounded]
      have nextBound : (bank I A O S blank selected).Bounded data radius
          {configuration with inputHead := min (configuration.inputHead+1) data.input.length} :=
        ⟨Nat.min_le_right _ _,bounded.auxiliary,bounded.index,bounded.head⟩
      have nextDistance : min (configuration.inputHead+1) data.input.length+remaining=data.input.length := by omega
      exact ih _ nextBound nextDistance

theorem scan_region {I A O S : Type} {k : ℕ} (blank : S) (selected : Fin k) (data : InputData I A)
    (choices : BitString) (radius : ℕ) (configuration : BankConfiguration O Unit S k)
    (bounded : (bank I A O S blank selected).Bounded data radius configuration) :
    (bank I A O S blank selected).RegionRun data choices radius configuration (.accepted configuration.output) := by
  have valid := bounded.input
  have path := scan_regionSteps blank selected data choices radius configuration bounded
    (data.input.length-configuration.inputHead) (by omega)
  refine ⟨data.input.length-configuration.inputHead,{configuration with inputHead := data.input.length},path,?_⟩
  apply TapeBank.Executes.accept
  simp [TapeBank.instruction,bank]

end ComplexityOfGenerators.Simulation.TransducerBank.InputEnd
