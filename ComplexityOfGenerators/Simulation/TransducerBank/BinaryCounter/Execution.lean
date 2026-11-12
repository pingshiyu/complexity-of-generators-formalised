import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Tape
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter

def carryOffset : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::rest => carryOffset rest+1

theorem carryOffset_bound (bits : List Bool) : carryOffset bits≤bits.length := by
  induction bits with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [carryOffset] <;> omega

theorem carry_steps {I A O : Type} (data : InputData I A) (choices : BitString)
    (low high : List Bool) :
    (bank I A O).Steps data choices (encoded (low++high) low.length .carry) (carryOffset high+1)
      (encoded (low++increment high) (low.length+carryOffset high) .rewind) := by
  induction high generalizing low with
  | nil =>
      have table : (bank I A O).instruction data (encoded (low++[]) low.length .carry)=
          .step .rewind (some true) .stay .stay .stay .stay none := by
        simpa only [List.head?_nil,reduceCtorEq,↓reduceIte] using (instruction_carry data low [])
      have path := TapeBank.Steps.single (bank I A O) data choices _ _ _ _ _ _ _ _ table
      rw [advance_write data low [] .carry .rewind true .stay low.length (by simp [Move.onInt])] at path
      simpa [increment,carryOffset] using path
  | cons first rest ih =>
      cases first with
      | false =>
          have table : (bank I A O).instruction data (encoded (low++false::rest) low.length .carry)=
              .step .rewind (some true) .stay .stay .stay .stay none := by simp [instruction_carry]
          have path := TapeBank.Steps.single (bank I A O) data choices _ _ _ _ _ _ _ _ table
          rw [advance_write data low (false::rest) .carry .rewind true .stay low.length (by simp [Move.onInt])] at path
          simpa [increment,carryOffset] using path
      | true =>
          have table : (bank I A O).instruction data (encoded (low++true::rest) low.length .carry)=
              .step .carry (some false) .right .stay .stay .stay none := by simp [instruction_carry]
          have path := TapeBank.Steps.single (bank I A O) data choices _ _ _ _ _ _ _ _ table
          rw [advance_write data low (true::rest) .carry .carry false .right (low.length+1)
            (by simp [Move.onInt])] at path
          have remaining := ih (low++[false])
          have aligned : (bank I A O).Steps data choices
              (encoded (low++false::rest) (low.length+1) .carry) (carryOffset rest+1)
              (encoded (low++false::increment rest) (low.length+1+carryOffset rest) .rewind) := by
            simpa [List.append_assoc] using remaining
          have both := path.trans (bank I A O) aligned
          simpa [carryOffset,increment,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using both

theorem rewind_steps {I A O : Type} (data : InputData I A) (choices : BitString)
    (bits : List Bool) (position : ℕ) :
    (bank I A O).Steps data choices (encoded bits position .rewind) (position+1) (encoded bits 0 .done) := by
  have path := TapeBank.rewind_steps (bank I A O) data choices .rewind .done 0 rfl
    (by intro input auxiliary index origin cell; rfl) position (encoded bits position .rewind)
    rfl rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  convert path using 1
  apply BankConfiguration.ext <;> try rfl
  funext index
  rw [one_index index]
  rfl

theorem increment_steps {I A O : Type} (data : InputData I A) (choices : BitString) (bits : List Bool) :
    (bank I A O).Steps data choices (encoded bits 0 .carry) (2*(carryOffset bits+1))
      (encoded (increment bits) 0 .done) := by
  have carried : (bank I A O).Steps data choices (encoded bits 0 .carry) (carryOffset bits+1)
      (encoded (increment bits) (carryOffset bits) .rewind) := by
    simpa using carry_steps data choices [] bits
  have path := carried.trans (bank I A O) (rewind_steps data choices (increment bits) (carryOffset bits))
  convert path using 1 <;> omega

theorem increment_executes {I A O : Type} (data : InputData I A) (choices : BitString) (bits : List Bool) :
    (bank I A O).Executes data choices (encoded bits 0 .carry) (2*(carryOffset bits+1)) (.accepted []) := by
  have finish : (bank I A O).Executes data choices (encoded (increment bits) 0 .done) 0 (.accepted []) := by
    apply TapeBank.Executes.accept
    rfl
  have execution := (increment_steps data choices bits).executes (bank I A O) finish
  convert execution using 1 <;> omega

/-- Repeated calls may reuse one fixed logarithmic work region. The bound
depends on the counter value, never on the number of surrounding steps. -/
theorem increment_region {I A O : Type} (data : InputData I A) (choices : BitString)
    (bits : List Bool) (canonical : Canonical bits) (bound : ℕ)
    (value : FixedBitBlocks.decode bits≤bound) :
    (bank I A O).RegionRun data choices (2*Nat.clog 2 (bound+1)+2) (encoded bits 0 .carry) (.accepted []) := by
  have small : FixedBitBlocks.decode bits<2^Nat.clog 2 (bound+1) := by
    have power := Nat.le_pow_clog (by decide : 1<2) (bound+1)
    omega
  have length := canonical_length_bound bits canonical _ small
  have offset := carryOffset_bound bits
  have initial : (bank I A O).Bounded data 0 (encoded bits 0 .carry) := by constructor <;> simp [encoded]
  have path := (increment_executes data choices bits).inRegion (bank I A O) initial
  exact path.mono (bank I A O) (by omega)

theorem increment_regionSteps {I A O : Type} (data : InputData I A) (choices : BitString)
    (bits : List Bool) (canonical : Canonical bits) (bound : ℕ)
    (value : FixedBitBlocks.decode bits≤bound) :
    (bank I A O).RegionSteps data choices (2*Nat.clog 2 (bound+1)+2) (encoded bits 0 .carry)
      (2*(carryOffset bits+1)) (encoded (increment bits) 0 .done) := by
  have small : FixedBitBlocks.decode bits<2^Nat.clog 2 (bound+1) := by
    have power := Nat.le_pow_clog (by decide : 1<2) (bound+1)
    omega
  have length := canonical_length_bound bits canonical _ small
  have offset := carryOffset_bound bits
  have initial : (bank I A O).Bounded data 0 (encoded bits 0 .carry) := by constructor <;> simp [encoded]
  exact ((increment_steps data choices bits).inRegion (bank I A O) 0 initial).mono (bank I A O) (by omega)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter
