import ComplexityOfGenerators.Simulation.TransducerBank.BankEmbedding

/-! A tape bank can occupy the left part of a larger bank. The unused right
bank is preserved, and a finite work-alphabet embedding adds no time or space. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.LeftBankEmbedding

variable {I A O Q S T : Type} {k l : ℕ}

open BankEmbedding (instruction)

set_option backward.isDefEq.respectTransparency false

def bank (source : TapeBank I A O Q S k) (l : ℕ) (encode : S → T) (decode : T → S) :
    TapeBank I A O Q T (k+l) where
  initial := source.initial
  blank := encode source.blank
  select := fun q => Fin.castAdd l (source.select q)
  transition := fun q i a x origin cell => instruction encode (source.transition q i a x origin (decode cell))

def lift (encode : S → T) (rightHead : Fin l → ℤ) (rightTape : Fin l → ℤ → T)
    (configuration : BankConfiguration O Q S k) : BankConfiguration O Q T (k+l) :=
  ⟨configuration.state,configuration.inputHead,configuration.auxiliaryHead,configuration.indexHead,
    configuration.randomHead,configuration.output,Fin.addCases configuration.head rightHead,
    Fin.addCases (fun j p => encode (configuration.tape j p)) rightTape⟩

theorem instruction_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (rightHead : Fin l → ℤ)
    (rightTape : Fin l → ℤ → T) (data : InputData I A) (c : BankConfiguration O Q S k) :
    (bank source l encode decode).instruction data (lift encode rightHead rightTape c) =
      instruction encode (source.instruction data c) := by
  simp only [TapeBank.instruction,bank,lift,Fin.addCases_left]
  rw [retract]

theorem advance_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (rightHead : Fin l → ℤ) (rightTape : Fin l → ℤ → T) (data : InputData I A)
    (c : BankConfiguration O Q S k) (next write work input auxiliary index emit) :
    (bank source l encode decode).advance data (lift encode rightHead rightTape c) next
        (encode write) work input auxiliary index emit =
      lift encode rightHead rightTape (source.advance data c next write work input auxiliary index emit) := by
  apply BankConfiguration.ext <;> try rfl
  · simp [TapeBank.advance,bank,lift,BankEmbedding.update_left]
  · simp only [TapeBank.advance,bank,lift,Fin.addCases_left,BankEmbedding.update_left]
    congr 1
    funext j p
    by_cases same : j=source.select c.state
    · subst j
      by_cases position : p=c.head (source.select c.state)
      · subst p
        simp
      · simp [Function.update_of_ne position]
    · simp [Function.update_of_ne same]

theorem choose_lift (encode : S → T) (rightHead : Fin l → ℤ) (rightTape : Fin l → ℤ → T)
    (c : BankConfiguration O Q S k) (next : Q) :
    TapeBank.choose (lift encode rightHead rightTape c) next =
      lift encode rightHead rightTape (TapeBank.choose c next) := rfl

theorem bounded_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (rightHead : Fin l → ℤ) (rightTape : Fin l → ℤ → T) (data : InputData I A) (radius : ℕ)
    (c : BankConfiguration O Q S k) (bounded : source.Bounded data radius c)
    (rightBound : ∀ j,(rightHead j).natAbs≤radius) :
    (bank source l encode decode).Bounded data radius (lift encode rightHead rightTape c) := by
  refine ⟨bounded.input,bounded.auxiliary,bounded.index,?_⟩
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa [lift] using bounded.head j
  · simpa [lift] using rightBound j

theorem steps_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (rightHead : Fin l → ℤ)
    (rightTape : Fin l → ℤ → T) {data : InputData I A} {bits : BitString}
    {start finish : BankConfiguration O Q S k} {ticks : ℕ}
    (path : source.Steps data bits start ticks finish) :
    (bank source l encode decode).Steps data bits (lift encode rightHead rightTape start)
      ticks (lift encode rightHead rightTape finish) := by
  induction path with
  | refl start => exact .refl _
  | random start no yes bit ticks finish table lookup rest ih =>
      apply TapeBank.Steps.random _ no yes bit ticks _
      · rw [instruction_lift source encode decode retract,table]; rfl
      · exact lookup
      · rw [choose_lift]; exact ih
  | step start next write work input auxiliary index emit ticks finish table rest ih =>
      apply TapeBank.Steps.step _ next (encode write) work input auxiliary index emit ticks _
      · rw [instruction_lift source encode decode retract,table]; rfl
      · rw [advance_lift]; exact ih

theorem regionSteps_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (rightHead : Fin l → ℤ)
    (rightTape : Fin l → ℤ → T) {data : InputData I A} {bits : BitString} {radius : ℕ}
    (rightBound : ∀ j,(rightHead j).natAbs≤radius)
    {start finish : BankConfiguration O Q S k} {ticks : ℕ}
    (path : source.RegionSteps data bits radius start ticks finish) :
    (bank source l encode decode).RegionSteps data bits radius (lift encode rightHead rightTape start)
      ticks (lift encode rightHead rightTape finish) := by
  induction path with
  | refl start bounded => exact .refl _ (bounded_lift source encode decode _ _ _ _ _ bounded rightBound)
  | random start no yes bit ticks finish bounded table lookup rest ih =>
      apply TapeBank.RegionSteps.random _ no yes bit ticks _
        (bounded_lift source encode decode _ _ _ _ _ bounded rightBound)
      · rw [instruction_lift source encode decode retract,table]; rfl
      · exact lookup
      · rw [choose_lift]; exact ih
  | step start next write work input auxiliary index emit ticks finish bounded table rest ih =>
      apply TapeBank.RegionSteps.step _ next (encode write) work input auxiliary index emit ticks _
        (bounded_lift source encode decode _ _ _ _ _ bounded rightBound)
      · rw [instruction_lift source encode decode retract,table]; rfl
      · rw [advance_lift]; exact ih

theorem executes_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (rightHead : Fin l → ℤ)
    (rightTape : Fin l → ℤ → T) {data : InputData I A} {bits : BitString}
    {start : BankConfiguration O Q S k} {ticks : ℕ} {result : Outcome O}
    (run : source.Executes data bits start ticks result) :
    (bank source l encode decode).Executes data bits (lift encode rightHead rightTape start) ticks result := by
  induction run with
  | accept start table =>
      apply TapeBank.Executes.accept
      rw [instruction_lift source encode decode retract,table]; rfl
  | reject start table =>
      apply TapeBank.Executes.reject
      rw [instruction_lift source encode decode retract,table]; rfl
  | exhausted start no yes table absent =>
      apply TapeBank.Executes.exhausted _ no yes
      · rw [instruction_lift source encode decode retract,table]; rfl
      · exact absent
  | random start no yes bit ticks result table lookup rest ih =>
      apply TapeBank.Executes.random _ no yes bit ticks result
      · rw [instruction_lift source encode decode retract,table]; rfl
      · exact lookup
      · rw [choose_lift]; exact ih
  | step start next write work input auxiliary index emit ticks result table rest ih =>
      apply TapeBank.Executes.step _ next (encode write) work input auxiliary index emit ticks result
      · rw [instruction_lift source encode decode retract,table]; rfl
      · rw [advance_lift]; exact ih

end ComplexityOfGenerators.Simulation.TransducerBank.LeftBankEmbedding
