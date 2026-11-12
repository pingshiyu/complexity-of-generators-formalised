import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Reset

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

 theorem configuration_bounded (copies radius : ℕ) (data : InputData I A) (phase : Phase Q copies)
    (length temporary digits : List Bool) (inputPosition : ℕ) (counterPosition clockPosition : ℤ)
    (ctor : BankConfiguration Unit Q S k) (input : inputPosition≤data.input.length)
    (heads : ∀j,(ctor.head j).natAbs≤radius)
    (counterBound : counterPosition.natAbs≤radius) (clockBound : clockPosition.natAbs≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).Bounded data radius
      (configuration C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) := by
  have bound := Capture.configuration_bounded (O:=O) C copies radius data .done length temporary digits
    inputPosition counterPosition clockPosition ctor input heads counterBound clockBound
  exact ⟨bound.input,bound.auxiliary,bound.index,bound.head⟩

 theorem prelude_configuration (copies : ℕ) (state : Prelude.Control) (length temporary digits : List Bool)
    (inputPosition : ℕ) (ctor : BankConfiguration Unit Q S k) :
    ((BankEmbedding.lift id ctor.head (fun j p=>(ctor.tape j p,((fun _=>none),none)))
      (LeftBankEmbedding.lift (Capture.encodeCounter C) (fun _ : Fin 1=>0)
        (fun _ p=>(C.blank,((fun _=>none),digitTape digits p)))
        (Prelude.configuration length temporary inputPosition state))).mapState Phase.prelude) =
      configuration (O:=O) C copies (.prelude state) length temporary digits inputPosition 0 0 ctor := by
  apply BankConfiguration.ext <;> try rfl
  all_goals funext index
  all_goals try (funext position)
  all_goals refine Fin.addCases (fun j=>?_) (fun j=>?_) index
  all_goals simp only [configuration,Capture.configuration,BankConfiguration.mapState,BankEmbedding.lift,
    LeftBankEmbedding.lift,Prelude.configuration,Capture.encodeCounter,id_eq,Fin.addCases_left,Fin.addCases_right]
  all_goals refine Fin.cases ?_ (fun j=>?_) j
  all_goals simp only [Capture.singleton_addCases,Fin.cases_zero,Fin.cases_succ]

 theorem initial_configuration (copies : ℕ) :
    (bank (I:=I) (A:=A) (O:=O) C copies).initialConfiguration=
      configuration C copies (.prelude (Prelude.bank I A O).initial) [] [] [] 0 0 0 C.initialConfiguration := by
  apply BankConfiguration.ext <;> try rfl
  all_goals funext index
  all_goals try (funext position)
  all_goals refine Fin.addCases (fun j=>?_) (fun j=>?_) index
  all_goals simp only [configuration,Capture.configuration,BankConfiguration.mapState,TapeBank.initialConfiguration,
    bank,Fin.addCases_left,Fin.addCases_right]
  all_goals refine Fin.cases ?_ (fun j=>?_) j
  all_goals simp [Fin.cases_zero,Fin.cases_succ,Prelude.memory,digitTape]

 theorem prelude_region (copies radius : ℕ) (data : InputData I A) (bits : BitString)
    (room : 2*Nat.clog 2 (data.input.length+1)+4≤radius) :
    ∃ ticks,(bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (bank (I:=I) (A:=A) (O:=O) C copies).initialConfiguration ticks
      (configuration C copies (.prelude .done) (increment^[data.input.length] []) [] [] 0 0 0 C.initialConfiguration) := by
  obtain ⟨ticks,path⟩ := Prelude.prepared_steps (O:=O) data bits
  have source := path.mono (Prelude.bank I A O) room
  have right := LeftBankEmbedding.regionSteps_lift (Prelude.bank I A O) (Capture.encodeCounter C)
    (fun cell=>cell.2.1) (by intro;rfl) (fun _ : Fin 1=>0)
    (fun _ p=>(C.blank,((fun _=>none),digitTape [] p))) (by intro;simp) source
  have lifted := BankEmbedding.regionSteps_lift
    (LeftBankEmbedding.bank (Prelude.bank I A O) 1 (Capture.encodeCounter C) (fun cell=>cell.2.1))
    id id (by intro;rfl) C.initialConfiguration.head
    (fun j p=>(C.initialConfiguration.tape j p,((fun _=>none),none)))
    (by intro;simp [TapeBank.initialConfiguration]) right
  have mapped := lifted.mapState (preludeBank (I:=I) (A:=A) (O:=O) C) (bank (I:=I) (A:=A) (O:=O) C copies)
    Phase.prelude (by intro;rfl)
    (by
      intro q i a x origin cell next write work move aux index emit table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.prelude (.seed (.write true 0)) cell) table)
    (by
      intro q i a x origin cell no yes table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.prelude (.seed (.write true 0)) cell) table)
  have initial : (Prelude.bank I A O).initialConfiguration=Prelude.configuration [] [] 0 (Prelude.bank I A O).initial := by
    apply BankConfiguration.ext <;> try rfl
    funext j p track
    simp [TapeBank.initialConfiguration,Prelude.bank,Prelude.configuration,Prelude.memory,digitTape]
  rw [initial,prelude_configuration C copies _ [] [] [] 0 C.initialConfiguration,
    prelude_configuration C copies .done _ [] [] 0 C.initialConfiguration] at mapped
  rw [←initial_configuration C copies] at mapped
  exact ⟨ticks,mapped⟩

 theorem go (copies radius : ℕ) (data : InputData I A) (bits : BitString)
    (phase next : Phase Q copies) (length temporary digits : List Bool) (inputPosition : ℕ)
    (counterPosition clockPosition : ℤ) (ctor : BankConfiguration Unit Q S k)
    (input : inputPosition≤data.input.length) (heads : ∀j,(ctor.head j).natAbs≤radius)
    (counterBound : counterPosition.natAbs≤radius) (clockBound : clockPosition.natAbs≤radius)
    (table : (bank (I:=I) (A:=A) (O:=O) C copies).instruction data
      (configuration C copies phase length temporary digits inputPosition counterPosition clockPosition ctor)=
      .step next ((configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).tape
        ((bank (I:=I) (A:=A) (O:=O) C copies).select phase)
        ((configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).head
          ((bank (I:=I) (A:=A) (O:=O) C copies).select phase))) .stay .stay .stay .stay none) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) 1
      (configuration C copies next length temporary digits inputPosition counterPosition clockPosition ctor) := by
  apply TapeBank.RegionSteps.step _ next _ .stay .stay .stay .stay none 0 _
    (configuration_bounded C copies radius data phase length temporary digits inputPosition counterPosition clockPosition ctor
      input heads counterBound clockBound) table
  have advanced := TapeBank.advance_stay (bank (I:=I) (A:=A) (O:=O) C copies) data
    (configuration C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) next
    input (Nat.zero_le _) (Nat.zero_le _)
  have same : (bank (I:=I) (A:=A) (O:=O) C copies).advance data
      (configuration C copies phase length temporary digits inputPosition counterPosition clockPosition ctor) next
      ((configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).tape
        ((bank (I:=I) (A:=A) (O:=O) C copies).select phase)
        ((configuration (O:=O) C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).head
          ((bank (I:=I) (A:=A) (O:=O) C copies).select phase))) .stay .stay .stay .stay none=
        configuration C copies next length temporary digits inputPosition counterPosition clockPosition ctor := by
    simpa only [configuration,BankConfiguration.mapState,Capture.configuration] using advanced
  rw [same]
  exact .refl _ (configuration_bounded C copies radius data next length temporary digits inputPosition counterPosition clockPosition ctor
      input heads counterBound clockBound)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation
