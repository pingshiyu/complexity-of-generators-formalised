import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

def writing (copies : ℕ) (next : Option QC) (remaining : Fin (copies+1)) :
    Control (QC:=QC) (Q:=Q) (S:=S) (O:=O) (k:=k) copies :=
  match next with | none=>.prefix remaining | some q=>.append q remaining

 theorem writing_select (copies : ℕ) (next : Option QC) (remaining : Fin (copies+1)) :
    (bank C B copies).select (writing copies next remaining)=clock (kc:=kc) (k:=k) := by
  cases next <;> rfl

 theorem writing_instruction (copies fuel index n : ℕ) (next : Option QC)
    (remaining : Fin (copies+1)) (ctor : BankConfiguration Unit QC SC kc) :
    (bank C B copies).instruction (generatorData n)
        (configuration C B copies (writing copies next remaining) fuel fuel index ctor) =
      if zero : remaining.val=0 then
        .step (.construct (next.getD C.initial)) (C.blank,Fuel.clockTape B fuel fuel)
          .stay .stay .stay .stay none
      else .step (writing copies next ⟨remaining.val-1,by omega⟩)
        (C.blank,.inr ()) .right .stay .stay .stay none := by
  cases next <;> simp only [TapeBank.instruction,configuration,writing,bank,clock,
    Fin.addCases_right,Fin.lastCases_last,Option.getD_none,Option.getD_some]

 theorem write_path (copies remaining fuel index n : ℕ) (next : Option QC)
    (ctor : BankConfiguration Unit QC SC kc) (count : remaining≤copies) (within : index≤n)
    (bits : BitString) :
    (bank C B copies).Steps (generatorData n) bits
      (configuration C B copies (writing copies next ⟨remaining,by omega⟩) fuel fuel index ctor)
      (remaining+1)
      (configuration C B copies (.construct (next.getD C.initial))
        (fuel+remaining) (fuel+remaining) index ctor) := by
  induction remaining generalizing fuel with
  | zero =>
      have first := TapeBank.Steps.single (bank C B copies) (generatorData n) bits
        (configuration C B copies (writing copies next ⟨0,by omega⟩) fuel fuel index ctor)
        (.construct (next.getD C.initial)) (C.blank,Fuel.clockTape B fuel fuel)
        .stay .stay .stay .stay none (by rw [writing_instruction]; simp)
      have cell : (C.blank,Fuel.clockTape B fuel fuel) =
          (configuration C B copies (writing copies next ⟨0,by omega⟩) fuel fuel index ctor).tape
            ((bank C B copies).select (writing copies next ⟨0,by omega⟩))
            ((configuration C B copies (writing copies next ⟨0,by omega⟩) fuel fuel index ctor).head
              ((bank C B copies).select (writing copies next ⟨0,by omega⟩))) := by
        simp only [configuration,writing_select,clock,Fin.addCases_right,Fin.lastCases_last]
      rw [cell,configuration_stay C B copies fuel fuel index n _ _ ctor within] at first
      simpa using first
  | succ remaining ih =>
      have first := TapeBank.Steps.single (bank C B copies) (generatorData n) bits
        (configuration C B copies (writing copies next ⟨remaining+1,by omega⟩) fuel fuel index ctor)
        (writing copies next ⟨remaining,by omega⟩) (C.blank,.inr ()) .right .stay .stay .stay none
        (by rw [writing_instruction]; simp)
      rw [configuration_writeClock C B copies fuel index n _ _ ctor within (writing_select C B copies next _)] at first
      have rest := ih (fuel+1) (by omega)
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using first.trans (bank C B copies) rest

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
