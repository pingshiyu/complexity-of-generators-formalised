import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

 theorem false_end (width : ℕ) : digitTape (List.replicate width false) width=none := by
  simp [digitTape]

 theorem zeros_region (copies remaining width radius : ℕ) (next : Q)
    (data : InputData I A) (bits : BitString) (length temporary : List Bool)
    (inputPosition : ℕ) (ctor : BankConfiguration Unit Q S k)
    (count : remaining≤copies) (input : inputPosition≤data.input.length)
    (heads : ∀ j,(ctor.head j).natAbs≤radius) (room : width+remaining≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data bits radius
      (configuration C copies (.zeros next ⟨remaining,by omega⟩) length temporary
        (List.replicate width false) inputPosition 0 width ctor) (remaining+1)
      (configuration C copies (.construct next) length temporary
        (List.replicate (width+remaining) false) inputPosition 0 (width+remaining) ctor) := by
  induction remaining generalizing width with
  | zero =>
      have bounded := configuration_bounded (O:=O) C copies radius data (.zeros next ⟨0,by omega⟩) length temporary
        (List.replicate width false) inputPosition 0 width ctor input heads (by simp) (by simpa using room)
      have table : (bank (I:=I) (A:=A) (O:=O) C copies).instruction data
          (configuration C copies (.zeros next ⟨0,by omega⟩) length temporary (List.replicate width false) inputPosition 0 width ctor)=
          .step (.construct next) (C.blank,((fun _=>none),none)) .stay .stay .stay .stay none := by
        simp only [TapeBank.instruction,configuration,bank,clock,Fin.addCases_right,Fin.cases_succ]
        simp [false_end]
      have cell : (C.blank,((fun _=>none),none))=
          (configuration (O:=O) C copies (.zeros next ⟨0,by omega⟩) length temporary (List.replicate width false) inputPosition 0 width ctor).tape
            ((bank (I:=I) (A:=A) (O:=O) C copies).select (.zeros next ⟨0,by omega⟩))
            ((configuration (O:=O) C copies (.zeros next ⟨0,by omega⟩) length temporary (List.replicate width false) inputPosition 0 width ctor).head
              ((bank (I:=I) (A:=A) (O:=O) C copies).select (.zeros next ⟨0,by omega⟩))) := by
        simp only [configuration,bank,clock,Fin.addCases_right,Fin.cases_succ,false_end]
      apply TapeBank.RegionSteps.step _ (.construct next) _ .stay .stay .stay .stay none 0 _ bounded table
      rw [cell,configuration_stay C copies data _ _ length temporary _ inputPosition 0 width ctor input]
      exact .refl _ (by simpa only [configuration] using bounded.with_state (bank (I:=I) (A:=A) (O:=O) C copies) (.construct next))
  | succ remaining ih =>
      have bounded := configuration_bounded (O:=O) C copies radius data (.zeros next ⟨remaining+1,by omega⟩) length temporary
        (List.replicate width false) inputPosition 0 width ctor input heads (by simp) (by simpa using Nat.le_trans (by omega : width≤width+(remaining+1)) room)
      have table : (bank (I:=I) (A:=A) (O:=O) C copies).instruction data
          (configuration C copies (.zeros next ⟨remaining+1,by omega⟩) length temporary (List.replicate width false) inputPosition 0 width ctor)=
          .step (.zeros next ⟨remaining,by omega⟩) (C.blank,((fun _=>none),some false)) .right .stay .stay .stay none := by
        simp only [TapeBank.instruction,configuration,bank,clock,Fin.addCases_right,Fin.cases_succ]
        simp
      apply TapeBank.RegionSteps.step _ (.zeros next ⟨remaining,by omega⟩) _ .right .stay .stay .stay none (remaining+1) _ bounded table
      have advance := configuration_append (O:=O) C copies data (.zeros next ⟨remaining+1,by omega⟩) (.zeros next ⟨remaining,by omega⟩)
        length temporary (List.replicate width false) inputPosition 0 ctor false .right input rfl
      simp only [List.length_replicate] at advance
      rw [advance]
      simpa [List.replicate_succ',Move.onInt,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm]
        using ih (width+1) (by omega) (by omega)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
