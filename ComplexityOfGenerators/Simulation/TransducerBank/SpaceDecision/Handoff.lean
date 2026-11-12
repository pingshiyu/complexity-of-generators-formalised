import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O QC SC QB SB : Type} {k m : ℕ}
    (constructor : TapeBank Unit Bool Unit QC SC k) (source : TapeBank I A O QB SB m)

private theorem cast_source (j : Fin m) :
    Fin.cast (tapeCount (m:=m) (k:=k)).symm (Fin.castAdd (k+2) j)=Fin.castAdd 1 (Fin.castAdd (k+1) j) := by
  apply Fin.ext
  rfl

private theorem cast_ctor (j : Fin k) :
    Fin.cast (tapeCount (m:=m) (k:=k)).symm (Fin.natAdd m (Fin.castAdd 2 j))=
      Fin.castAdd 1 (Fin.natAdd m (Fin.castAdd 1 j)) := by
  apply Fin.ext
  rfl

private theorem cast_counter :
    Fin.cast (tapeCount (m:=m) (k:=k)).symm (Fin.natAdd m (Fin.natAdd k (0 : Fin 2)))=
      Fin.castAdd 1 (Fin.natAdd m (Fin.natAdd k (0 : Fin 1))) := by
  apply Fin.ext
  simp

private theorem cast_clock :
    Fin.cast (tapeCount (m:=m) (k:=k)).symm (Fin.natAdd m (Fin.natAdd k (Fin.succ (0 : Fin 1))))=
      Fin.natAdd (m+(k+1)) (0 : Fin 1) := by
  apply Fin.ext
  simp

/-- The retained constructor/length work is exactly the passive right frame
of the clock's source bank. The final tape is the same physical clock lane. -/
theorem handoff_configuration (copies length : ℕ) (digits : List Bool) (ctor : BankConfiguration Unit QC SC k) :
    {initialConfiguration constructor source copies length digits ctor with state:=Sum.inr (source.initial,.check)}=
      clockConfiguration constructor source copies length digits ctor .check := by
  apply BankConfiguration.ext <;> try rfl
  · funext tape
    refine Fin.addCases (fun j=>?_) (fun j=>?_) tape
    · simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
        BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
        BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,frameHead,cast_source,
        TapeBank.initialConfiguration]
    · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
      · simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
          BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
          BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,frameHead,cast_ctor]
      · refine Fin.cases ?_ (fun j=>?_) j
        · simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
            BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
            BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,frameHead,cast_counter]
        · have zero : j=0 := Subsingleton.elim _ _
          subst j
          simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
            BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
            BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,frameHead,cast_clock]
  · funext tape position
    refine Fin.addCases (fun j=>?_) (fun j=>?_) tape
    · simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
        BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
        BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,
        frameTape,cast_source,TapeBank.initialConfiguration,sourceBank,LeftBankEmbedding.bank,
        encodeInitial,encodeSource]
    · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
      · simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
          BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
          BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,
          frameTape,cast_ctor,encodeInitial]
      · refine Fin.cases ?_ (fun j=>?_) j
        · simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
            BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
            BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,
            frameTape,cast_counter,encodeInitial]
        · have zero : j=0 := Subsingleton.elim _ _
          subst j
          simp only [Fin.addCases_left,Fin.addCases_right,Fin.cases_zero,Fin.cases_succ,initialConfiguration,clockConfiguration,sourceConfiguration,BankConfiguration.mapState,
            BankEmbedding.lift,LeftBankEmbedding.lift,BinaryClock.configuration,TapeCast.configuration,
            BinaryClockInitialisation.configuration,BinaryClockInitialisation.Capture.configuration,
            frameTape,cast_clock,encodeInitial,sourceBank,LeftBankEmbedding.bank,encodeSource]

/-- A single real transition joins clock construction to source execution. -/
theorem handoff_path (copies length : ℕ) (digits : List Bool) (ctor : BankConfiguration Unit QC SC k)
    (data : InputData I A) (choices : BitString) (radius : ℕ)
    (bounded : (bank constructor source copies).Bounded data radius (initialConfiguration constructor source copies length digits ctor)) :
    (bank constructor source copies).RegionSteps data choices radius
      (initialConfiguration constructor source copies length digits ctor) 1
      (clockConfiguration constructor source copies length digits ctor .check) := by
  let start := initialConfiguration constructor source copies length digits ctor
  let next : Control QC QB copies := Sum.inr (source.initial,.check)
  have table : (bank constructor source copies).instruction data start=
      .step next (start.tape ((bank constructor source copies).select start.state)
        (start.head ((bank constructor source copies).select start.state))) .stay .stay .stay .stay none := rfl
  have nextBound : (bank constructor source copies).Bounded data radius {start with state:=next} :=
    ⟨bounded.input,bounded.auxiliary,bounded.index,bounded.head⟩
  have equal : {start with state:=next}=clockConfiguration constructor source copies length digits ctor .check :=
    handoff_configuration constructor source copies length digits ctor
  apply TapeBank.RegionSteps.step start next _ .stay .stay .stay .stay none 0 _ bounded table
  rw [TapeBank.advance_stay (bank constructor source copies) data start next bounded.input bounded.auxiliary bounded.index,equal]
  rw [equal] at nextBound
  exact .refl _ nextBound

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
