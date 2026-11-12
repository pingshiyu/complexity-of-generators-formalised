import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Constructor
import ComplexityOfGenerators.Simulation.TransducerBank.RegionRewind

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

 theorem rewind_clock_region (copies radius position : ℕ) (data : InputData I A) (bits : BitString)
    (length temporary digits : List Bool) (inputPosition : ℕ) (ctor : BankConfiguration Unit Q S k)
    (input : inputPosition≤data.input.length) (heads : ∀j,(ctor.head j).natAbs≤radius) (room : position≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies .rewindClock length temporary digits inputPosition 0 position ctor)
      (position+1) (configuration C copies .seekEnd length temporary digits inputPosition 0 0 ctor) := by
  have path := TapeBank.rewind_regionSteps (bank (I:=I) (A:=A) (O:=O) C copies) data bits
    .rewindClock .seekEnd (clock (k:=k)) rfl (by intro i a x origin cell;cases origin <;> rfl)
    position radius (configuration C copies .rewindClock length temporary digits inputPosition 0 position ctor) rfl
    (by simp only [configuration,clock,Fin.addCases_right,Fin.cases_succ])
    (configuration_bounded (O:=O) C copies radius data .rewindClock length temporary digits inputPosition 0 position ctor
      input heads (by simp) (by simpa using room))
  convert path using 1
  apply BankConfiguration.ext <;> try rfl
  case head =>
    simp only [configuration,clock,BankEmbedding.update_right]
    funext j
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
      refine Fin.cases ?_ (fun j=>?_) j
      · simp [Function.update]
      · have zero : j=0 := Fin.eq_zero j
        subst j
        simp only [Function.update_self,Fin.cases_succ]

 theorem constructor_accept_instruction (copies : ℕ) (data : InputData I A)
    (length temporary digits : List Bool) (ctor : BankConfiguration Unit Q S k)
    (table : C.instruction (decisionData (List.replicate data.input.length ())) ctor=.accept) :
    (bank (I:=I) (A:=A) (O:=O) C copies).instruction data
      (configuration C copies (.construct ctor.state) length temporary digits ctor.inputHead 0 digits.length ctor)=
      .step .writeLast (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state)),((fun _=>none),none))
        .stay .stay .stay .stay none := by
  simp only [TapeBank.instruction,decisionData,List.getElem?_nil,Nat.not_lt_zero,ite_false] at table
  simp only [TapeBank.instruction,configuration,bank,Fin.addCases_left,unary_input_map]
  rw [table]

 theorem finish_region (copies radius width : ℕ) (data : InputData I A) (bits : BitString)
    (length temporary : List Bool) (ctor : BankConfiguration Unit Q S k)
    (input : ctor.inputHead≤data.input.length) (heads : ∀j,(ctor.head j).natAbs≤radius) (room : width≤radius)
    (table : C.instruction (decisionData (List.replicate data.input.length ())) ctor=.accept) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies (.construct ctor.state) length temporary (List.replicate width false) ctor.inputHead 0 width ctor)
      (2+(width+1))
      (configuration C copies .seekEnd length temporary (List.replicate width false++[true]) ctor.inputHead 0 0 ctor) := by
  have beforeBound := configuration_bounded (O:=O) C copies radius data (.construct ctor.state) length temporary
    (List.replicate width false) ctor.inputHead 0 width ctor input heads (by simp) (by simpa using room)
  have toWrite : (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies (.construct ctor.state) length temporary (List.replicate width false) ctor.inputHead 0 width ctor) 1
      (configuration C copies .writeLast length temporary (List.replicate width false) ctor.inputHead 0 width ctor) := by
    have acceptTable := constructor_accept_instruction (O:=O) C copies data length temporary (List.replicate width false) ctor table
    simp only [List.length_replicate] at acceptTable
    apply TapeBank.RegionSteps.step _ .writeLast _ .stay .stay .stay .stay none 0 _ beforeBound acceptTable
    have cell : (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state)),((fun _=>none),none))=
      (configuration (O:=O) C copies (.construct ctor.state) length temporary (List.replicate width false) ctor.inputHead 0 width ctor).tape
        ((bank (I:=I) (A:=A) (O:=O) C copies).select (.construct ctor.state))
        ((configuration (O:=O) C copies (.construct ctor.state) length temporary (List.replicate width false) ctor.inputHead 0 width ctor).head
          ((bank (I:=I) (A:=A) (O:=O) C copies).select (.construct ctor.state))) := by
      simp only [configuration,bank,Fin.addCases_left]
    rw [cell,configuration_stay C copies data _ _ length temporary _ ctor.inputHead 0 width ctor input]
    exact .refl _ (configuration_bounded C copies radius data .writeLast length temporary _ ctor.inputHead 0 width ctor input heads (by simp) (by simpa using room))
  have write : (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies .writeLast length temporary (List.replicate width false) ctor.inputHead 0 width ctor) 1
      (configuration C copies .rewindClock length temporary (List.replicate width false++[true]) ctor.inputHead 0 width ctor) := by
    apply TapeBank.RegionSteps.step _ .rewindClock _ .stay .stay .stay .stay none 0 _
      (configuration_bounded C copies radius data .writeLast length temporary _ ctor.inputHead 0 width ctor input heads (by simp) (by simpa using room)) rfl
    have advanced := configuration_append (O:=O) C copies data .writeLast .rewindClock length temporary
      (List.replicate width false) ctor.inputHead 0 ctor true .stay input rfl
    simp only [List.length_replicate,Move.onInt] at advanced
    rw [advanced]
    exact .refl _ (configuration_bounded C copies radius data .rewindClock length temporary _ ctor.inputHead 0 width ctor input heads (by simp) (by simpa using room))
  have rewind := rewind_clock_region (O:=O) C copies radius width data bits length temporary
    (List.replicate width false++[true]) ctor.inputHead ctor input heads room
  simpa [←Nat.add_assoc] using (toWrite.trans (bank (I:=I) (A:=A) (O:=O) C copies) write).trans
    (bank (I:=I) (A:=A) (O:=O) C copies) rewind

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
