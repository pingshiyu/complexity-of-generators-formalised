import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Prelude

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

theorem cases_one {α : Type} (first : α) (rest : Fin 1→α) :
    Fin.cases (motive:=fun _ : Fin 2=>α) first rest (1:Fin 2)=rest 0 := by
  change Fin.cases first rest (Fin.succ 0)=rest 0
  rw [Fin.cases_succ]

def emptyFrame : LogSeed.Frame := ⟨fun _ _=>none,fun _=>none,fun _ _=>none⟩

 theorem seed_configuration (copies : ℕ) (state : LogSeed.Control copies)
    (length digits : List Bool) (counterPosition clockPosition : ℕ) (ctor : BankConfiguration Unit Q S k) :
    (BankEmbedding.lift (fun value=>(C.blank,value)) ctor.head
      (fun j p=>(ctor.tape j p,((fun _=>none),none)))
      (LogSeed.encoded emptyFrame length digits counterPosition clockPosition state)).mapState Phase.seed=
      configuration (O:=O) C copies (.seed state) length [] digits 0 counterPosition clockPosition ctor := by
  apply BankConfiguration.ext <;> try rfl
  all_goals funext index
  all_goals try (funext position)
  all_goals refine Fin.addCases (fun j=>?_) (fun j=>?_) index
  all_goals simp only [configuration,Capture.configuration,BankConfiguration.mapState,BankEmbedding.lift,
    Fin.addCases_left,Fin.addCases_right]
  all_goals refine Fin.cases ?_ (fun j=>?_) j
  all_goals try (have zero : j=0 := Fin.eq_zero j;subst j)
  all_goals simp [LogSeed.encoded,LogSeed.counterTape,LogSeed.clockTape,emptyFrame,
    Prelude.memory_empty_temporary,Fin.cases_zero,cases_one]

 theorem seed_region (copies radius : ℕ) (data : InputData I A) (bits : BitString)
    (length : List Bool) (ctor : BankConfiguration Unit Q S k)
    (heads : ∀j,(ctor.head j).natAbs≤radius) (room : (copies+5)*(length.length+1)≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies (.seed (.write true 0)) length [] [] 0 0 0 ctor)
      (copies+1+((copies+3)*length.length+1)+(length.length+1))
      (configuration C copies (.seed .done) length [] (List.replicate (copies*(length.length+1)) false)
        0 0 (copies*(length.length+1)) ctor) := by
  have path := (LogSeed.routine_regionSteps (O:=O) copies emptyFrame data bits length).mono (LogSeed.bank I A O copies) room
  have lifted := BankEmbedding.regionSteps_lift (LogSeed.bank I A O copies) (fun value=>(C.blank,value)) Prod.snd
    (by intro;rfl) ctor.head (fun j p=>(ctor.tape j p,((fun _=>none),none))) heads path
  have mapped := lifted.mapState (seedBank (I:=I) (A:=A) (O:=O) C copies) (bank (I:=I) (A:=A) (O:=O) C copies)
    Phase.seed (by intro;rfl)
    (by
      intro q i a x origin cell next write work move aux index emit table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.seed (.capture (.construct C.initial)) cell) table)
    (by
      intro q i a x origin cell no yes table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.seed (.capture (.construct C.initial)) cell) table)
  simpa only [seed_configuration,Nat.cast_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using mapped

 theorem prelude_to_seed (copies radius : ℕ) (data : InputData I A) (bits : BitString)
    (length : List Bool) (ctor : BankConfiguration Unit Q S k) (heads : ∀j,(ctor.head j).natAbs≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies (.prelude .done) length [] [] 0 0 0 ctor) 1
      (configuration C copies (.seed (.write true 0)) length [] [] 0 0 0 ctor) :=
  go C copies radius data bits _ _ length [] [] 0 0 0 ctor (Nat.zero_le _) heads (by simp) (by simp) rfl

 theorem seed_to_capture (copies radius : ℕ) (data : InputData I A) (bits : BitString)
    (length : List Bool) (ctor : BankConfiguration Unit Q S k) (heads : ∀j,(ctor.head j).natAbs≤radius)
    (room : copies*(length.length+1)≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies (.seed .done) length [] (List.replicate (copies*(length.length+1)) false)
        0 0 (copies*(length.length+1)) ctor) 1
      (configuration C copies (.capture (.construct C.initial)) length [] (List.replicate (copies*(length.length+1)) false)
        0 0 (copies*(length.length+1)) ctor) :=
  go C copies radius data bits _ _ length [] _ 0 0 _ ctor (Nat.zero_le _) heads (by simp) (by
    have cast : (copies:ℤ)*((length.length:ℤ)+1)=((copies*(length.length+1):ℕ):ℤ) := by push_cast; rfl
    rw [cast,Int.natAbs_natCast]
    exact room) rfl

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation
