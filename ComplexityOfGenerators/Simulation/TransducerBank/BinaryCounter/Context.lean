import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter

structure Context (O : Type) where
  inputHead : ℕ := 0
  auxiliaryHead : ℕ := 0
  indexHead : ℕ := 0
  randomHead : ℕ := 0
  output : List O := []

def Context.Valid {I A O : Type} (context : Context O) (data : InputData I A) : Prop :=
  context.inputHead≤data.input.length ∧ context.auxiliaryHead≤data.auxiliary.length ∧ context.indexHead≤data.index

def withContext {O : Type} (context : Context O) (configuration : BankConfiguration O Phase (Option Bool) 1) :
    BankConfiguration O Phase (Option Bool) 1 :=
  {configuration with
    inputHead := context.inputHead
    auxiliaryHead := context.auxiliaryHead
    indexHead := context.indexHead
    randomHead := context.randomHead
    output := context.output}

theorem instruction_context {I A O : Type} (data : InputData I A) (context : Context O)
    (configuration : BankConfiguration O Phase (Option Bool) 1) :
    (bank I A O).instruction data (withContext context configuration)=(bank I A O).instruction data configuration := rfl

theorem advance_context {I A O : Type} (data : InputData I A) (context : Context O)
    (valid : context.Valid data) (configuration : BankConfiguration O Phase (Option Bool) 1)
    (next write work) :
    (bank I A O).advance data (withContext context configuration) next write work .stay .stay .stay none=
      withContext context ((bank I A O).advance data configuration next write work .stay .stay .stay none) := by
  rcases valid with ⟨input,auxiliary,index⟩
  apply BankConfiguration.ext <;>
    simp [TapeBank.advance,withContext,Move.onInput,Nat.min_eq_left input,
      Nat.min_eq_left auxiliary,Nat.min_eq_left index]

theorem instruction_work_only {I A O : Type} (data : InputData I A)
    (configuration : BankConfiguration O Phase (Option Bool) 1) :
    match (bank I A O).instruction data configuration with
    | .step _ _ _ input auxiliary index emit => input=.stay ∧ auxiliary=.stay ∧ index=.stay ∧ emit=none
    | _ => True := by
  cases state : configuration.state <;>
    by_cases good : configuration.tape 0 (configuration.head 0)=some true <;>
    simp [TapeBank.instruction,bank,transition,state,good]

theorem instruction_not_random {I A O : Type} (data : InputData I A)
    (configuration : BankConfiguration O Phase (Option Bool) 1) :
    match (bank I A O).instruction data configuration with | .readRandom _ _ => False | _ => True := by
  cases state : configuration.state <;>
    by_cases good : configuration.tape 0 (configuration.head 0)=some true <;>
    simp [TapeBank.instruction,bank,transition,state,good]

theorem context_steps {I A O : Type} (data : InputData I A) (choices : BitString)
    (context : Context O) (valid : context.Valid data)
    {source target : BankConfiguration O Phase (Option Bool) 1} {time : ℕ}
    (path : (bank I A O).Steps data choices source time target) :
    (bank I A O).Steps data choices (withContext context source) time (withContext context target) := by
  induction path with
  | refl source => exact .refl _
  | random source no yes bit time target table lookup rest ih =>
      have never := instruction_not_random data source
      simp [table] at never
  | step source next write work input auxiliary index emit time target table rest ih =>
      have moves := instruction_work_only data source
      rw [table] at moves
      obtain ⟨rfl,rfl,rfl,rfl⟩ := moves
      apply TapeBank.Steps.step (withContext context source) next write work .stay .stay .stay none time
        (withContext context target)
      · rw [instruction_context]
        exact table
      · rw [advance_context data context valid]
        exact ih

theorem context_bounded {I A O : Type} (data : InputData I A) (context : Context O)
    (valid : context.Valid data) (radius : ℕ) (configuration : BankConfiguration O Phase (Option Bool) 1)
    (bounded : (bank I A O).Bounded data radius configuration) :
    (bank I A O).Bounded data radius (withContext context configuration) :=
  ⟨valid.1,valid.2.1,valid.2.2,bounded.head⟩

theorem context_regionSteps {I A O : Type} (data : InputData I A) (choices : BitString)
    (context : Context O) (valid : context.Valid data)
    {radius time : ℕ} {source target : BankConfiguration O Phase (Option Bool) 1}
    (path : (bank I A O).RegionSteps data choices radius source time target) :
    (bank I A O).RegionSteps data choices radius (withContext context source) time (withContext context target) := by
  induction path with
  | refl source bounded => exact .refl _ (context_bounded data context valid radius source bounded)
  | random source no yes bit time target bounded table lookup rest ih =>
      have never := instruction_not_random data source
      simp [table] at never
  | step source next write work input auxiliary index emit time target bounded table rest ih =>
      have moves := instruction_work_only data source
      rw [table] at moves
      obtain ⟨rfl,rfl,rfl,rfl⟩ := moves
      apply TapeBank.RegionSteps.step (withContext context source) next write work .stay .stay .stay none time
        (withContext context target) (context_bounded data context valid radius source bounded)
      · rw [instruction_context]
        exact table
      · rw [advance_context data context valid]
        exact ih

theorem increment_context_region {I A O : Type} (data : InputData I A) (choices : BitString)
    (context : Context O) (valid : context.Valid data) (bits : List Bool) (canonical : Canonical bits)
    (bound : ℕ) (value : FixedBitBlocks.decode bits≤bound) :
    (bank I A O).RegionRun data choices (2*Nat.clog 2 (bound+1)+2)
      (withContext context (encoded bits 0 .carry)) (.accepted context.output) := by
  have path := increment_regionSteps (O:=O) data choices bits canonical bound value
  refine ⟨_,withContext context (encoded (increment bits) 0 .done),
    context_regionSteps data choices context valid path,?_⟩
  apply TapeBank.Executes.accept
  rfl

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter
