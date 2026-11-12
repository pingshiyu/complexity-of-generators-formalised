import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import Mathlib.Data.Fin.Tuple.Basic

/-! A tape bank can occupy the right part of a larger bank. The unused left
bank is preserved, and a finite work-alphabet embedding adds no time or space. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BankEmbedding

variable {I A O Q S T : Type} {k l : ℕ}

theorem update_right {α : Type} (left : Fin l → α) (right : Fin k → α)
    (j : Fin k) (value : α) :
    Function.update (Fin.addCases (motive := fun _ => α) left right) (Fin.natAdd l j) value =
      Fin.addCases (motive := fun _ => α) left (Function.update right j value) := by
  funext index
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp [Function.update, Fin.ext_iff]
    omega
  · simp [Function.update, Fin.ext_iff]

theorem update_left {α : Type} (left : Fin l → α) (right : Fin k → α)
    (j : Fin l) (value : α) :
    Function.update (Fin.addCases (motive := fun _ => α) left right) (Fin.castAdd k j) value =
      Fin.addCases (motive := fun _ => α) (Function.update left j value) right := by
  funext index
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp [Function.update, Fin.ext_iff]
  · simp [Function.update, Fin.ext_iff]
    omega

def instruction (encode : S → T) : BankInstruction Q S O → BankInstruction Q T O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom no yes
  | .step next write work input auxiliary index emit =>
      .step next (encode write) work input auxiliary index emit

def bank (source : TapeBank I A O Q S k) (l : ℕ) (encode : S → T) (decode : T → S) :
    TapeBank I A O Q T (l+k) where
  initial := source.initial
  blank := encode source.blank
  select := fun q => Fin.natAdd l (source.select q)
  transition := fun q i a x origin cell => instruction encode (source.transition q i a x origin (decode cell))

def lift (encode : S → T) (leftHead : Fin l → ℤ) (leftTape : Fin l → ℤ → T)
    (configuration : BankConfiguration O Q S k) : BankConfiguration O Q T (l+k) :=
  ⟨configuration.state,configuration.inputHead,configuration.auxiliaryHead,configuration.indexHead,
    configuration.randomHead,configuration.output,Fin.addCases leftHead configuration.head,
    Fin.addCases leftTape (fun j p => encode (configuration.tape j p))⟩

theorem instruction_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (leftHead : Fin l → ℤ)
    (leftTape : Fin l → ℤ → T) (data : InputData I A) (c : BankConfiguration O Q S k) :
    (bank source l encode decode).instruction data (lift encode leftHead leftTape c) =
      instruction encode (source.instruction data c) := by
  simp only [TapeBank.instruction,bank,lift,Fin.addCases_right]
  rw [retract]
  rfl

theorem advance_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (leftHead : Fin l → ℤ) (leftTape : Fin l → ℤ → T) (data : InputData I A)
    (c : BankConfiguration O Q S k) (next write work input auxiliary index emit) :
    (bank source l encode decode).advance data (lift encode leftHead leftTape c) next
        (encode write) work input auxiliary index emit =
      lift encode leftHead leftTape (source.advance data c next write work input auxiliary index emit) := by
  apply BankConfiguration.ext <;> try rfl
  · simp [TapeBank.advance,bank,lift,update_right]
  · simp only [TapeBank.advance,bank,lift,Fin.addCases_right,update_right]
    congr 1
    funext j p
    by_cases same : j=source.select c.state
    · subst j
      by_cases position : p=c.head (source.select c.state)
      · subst p
        simp
      · simp [Function.update_of_ne position]
    · simp [Function.update_of_ne same]

theorem choose_lift (encode : S → T) (leftHead : Fin l → ℤ) (leftTape : Fin l → ℤ → T)
    (c : BankConfiguration O Q S k) (next : Q) :
    TapeBank.choose (lift encode leftHead leftTape c) next =
      lift encode leftHead leftTape (TapeBank.choose c next) := rfl

theorem bounded_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (leftHead : Fin l → ℤ) (leftTape : Fin l → ℤ → T) (data : InputData I A) (radius : ℕ)
    (c : BankConfiguration O Q S k) (bounded : source.Bounded data radius c)
    (leftBound : ∀ j,(leftHead j).natAbs≤radius) :
    (bank source l encode decode).Bounded data radius (lift encode leftHead leftTape c) := by
  refine ⟨bounded.input,bounded.auxiliary,bounded.index,?_⟩
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa [lift] using leftBound j
  · simpa [lift] using bounded.head j

theorem steps_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (leftHead : Fin l → ℤ)
    (leftTape : Fin l → ℤ → T) {data : InputData I A} {bits : BitString}
    {start finish : BankConfiguration O Q S k} {ticks : ℕ}
    (path : source.Steps data bits start ticks finish) :
    (bank source l encode decode).Steps data bits (lift encode leftHead leftTape start)
      ticks (lift encode leftHead leftTape finish) := by
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
    (retract : Function.LeftInverse decode encode) (leftHead : Fin l → ℤ)
    (leftTape : Fin l → ℤ → T) {data : InputData I A} {bits : BitString} {radius : ℕ}
    (leftBound : ∀ j,(leftHead j).natAbs≤radius)
    {start finish : BankConfiguration O Q S k} {ticks : ℕ}
    (path : source.RegionSteps data bits radius start ticks finish) :
    (bank source l encode decode).RegionSteps data bits radius (lift encode leftHead leftTape start)
      ticks (lift encode leftHead leftTape finish) := by
  induction path with
  | refl start bounded => exact .refl _ (bounded_lift source encode decode _ _ _ _ _ bounded leftBound)
  | random start no yes bit ticks finish bounded table lookup rest ih =>
      apply TapeBank.RegionSteps.random _ no yes bit ticks _
        (bounded_lift source encode decode _ _ _ _ _ bounded leftBound)
      · rw [instruction_lift source encode decode retract,table]; rfl
      · exact lookup
      · rw [choose_lift]; exact ih
  | step start next write work input auxiliary index emit ticks finish bounded table rest ih =>
      apply TapeBank.RegionSteps.step _ next (encode write) work input auxiliary index emit ticks _
        (bounded_lift source encode decode _ _ _ _ _ bounded leftBound)
      · rw [instruction_lift source encode decode retract,table]; rfl
      · rw [advance_lift]; exact ih

theorem executes_lift (source : TapeBank I A O Q S k) (encode : S → T) (decode : T → S)
    (retract : Function.LeftInverse decode encode) (leftHead : Fin l → ℤ)
    (leftTape : Fin l → ℤ → T) {data : InputData I A} {bits : BitString}
    {start : BankConfiguration O Q S k} {ticks : ℕ} {result : Outcome O}
    (run : source.Executes data bits start ticks result) :
    (bank source l encode decode).Executes data bits (lift encode leftHead leftTape start) ticks result := by
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

end ComplexityOfGenerators.Simulation.TransducerBank.BankEmbedding
