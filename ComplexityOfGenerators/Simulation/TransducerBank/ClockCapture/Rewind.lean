import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Constructor

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

 theorem rewind_path (copies fuel cursor index n : ℕ)
    (ctor : BankConfiguration Unit QC SC kc) (within : index≤n) (bits : BitString) :
    (bank C B copies).Steps (generatorData n) bits
      (configuration C B copies .rewind fuel cursor index ctor) (cursor+1)
      (configuration C B copies (.source (.fetch B.initial)) fuel 0 (index-cursor) ctor) := by
  induction cursor generalizing index with
  | zero =>
      have first := TapeBank.Steps.single (bank C B copies) (generatorData n) bits
        (configuration C B copies .rewind fuel 0 index ctor) (.source (.fetch B.initial))
        (C.blank,Fuel.clockTape B fuel 0) .stay .stay .stay .stay none (by
          simp only [TapeBank.instruction,configuration,bank,clock,Fin.addCases_right,Fin.lastCases_last]
          simp)
      have cell : (C.blank,Fuel.clockTape B fuel 0) =
          (configuration C B copies .rewind fuel 0 index ctor).tape
            ((bank C B copies).select .rewind)
            ((configuration C B copies .rewind fuel 0 index ctor).head ((bank C B copies).select .rewind)) := by
        simp only [configuration,bank,clock,Fin.addCases_right,Fin.lastCases_last,Nat.cast_zero]
      rw [cell,configuration_stay C B copies fuel 0 index n _ _ ctor within] at first
      simpa using first
  | succ cursor ih =>
      have first := TapeBank.Steps.single (bank C B copies) (generatorData n) bits
        (configuration C B copies .rewind fuel (cursor+1) index ctor) .rewind
        (C.blank,Fuel.clockTape B fuel (cursor+1)) .left .stay .stay .left none (by
          simp only [TapeBank.instruction,configuration,bank,clock,Fin.addCases_right,Fin.lastCases_last]
          simp
          omega)
      have cell : (C.blank,Fuel.clockTape B fuel (cursor+1)) =
          (configuration C B copies .rewind fuel (cursor+1) index ctor).tape
            (clock (kc:=kc) (k:=k)) (cursor+1) := by
        simp only [configuration,clock,Fin.addCases_right,Fin.lastCases_last,Nat.cast_add,Nat.cast_one]
      rw [cell,configuration_rewind C B copies fuel cursor index n ctor within] at first
      have rest := ih (index-1) (by omega)
      simpa [Nat.add_assoc,Nat.sub_sub,Nat.add_comm] using first.trans (bank C B copies) rest

 theorem initial_configuration (copies : ℕ) :
    (bank C B copies).initialConfiguration =
      configuration C B copies (.prefix ⟨copies,by omega⟩) 0 0 0 C.initialConfiguration := by
  apply BankConfiguration.ext <;> try rfl
  case head =>
    funext j
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simp [TapeBank.initialConfiguration,configuration]
    · simp only [TapeBank.initialConfiguration,configuration,Fin.addCases_right]
      refine Fin.lastCases ?_ (fun j=>?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc,Nat.cast_zero]
  case tape =>
    funext j p
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simp [TapeBank.initialConfiguration,configuration,bank]
    · simp only [TapeBank.initialConfiguration,configuration,bank,Fin.addCases_right]
      refine Fin.lastCases ?_ (fun j=>?_) j <;>
        simp only [Fin.lastCases_last,Fin.lastCases_castSucc,Fuel.clockTape]
      split_ifs with inside
      · omega
      · rfl

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
