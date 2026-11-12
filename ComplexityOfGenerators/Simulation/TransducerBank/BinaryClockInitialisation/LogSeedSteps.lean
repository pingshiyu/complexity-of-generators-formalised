import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.LogSeed

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.LogSeed

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

theorem write_steps {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (counter clock : List Bool) (counterPosition : ℕ) (initial : Bool) (position : Fin (constant+1))
    (remaining : ℕ) (distance : position.val+remaining=constant) :
    (bank I A O constant).Steps data choices (encoded frame counter clock counterPosition clock.length (.write initial position))
      (remaining+1) (encoded frame counter (clock++List.replicate remaining false) counterPosition (clock.length+remaining)
        (if initial then .read else .advance)) := by
  induction remaining generalizing position clock with
  | zero =>
      have complete : ¬position.val<constant := by omega
      have path := go (O:=O) constant frame data choices counter clock counterPosition clock.length (.write initial position)
        (if initial then .read else .advance) (by simp [TapeBank.instruction,bank,selected,transition,encoded,complete])
      simpa using path
  | succ remaining ih =>
      have more : position.val<constant := by omega
      let next : Fin (constant+1) := ⟨position.val+1,by omega⟩
      have table : (bank I A O constant).instruction data
          (encoded frame counter clock counterPosition clock.length (.write initial position))=
          .step (.write initial next) (frame.clockTracks clock.length,some false) .right .stay .stay .stay none := by
        simp [TapeBank.instruction,bank,selected,transition,encoded,clockTape,more,next]
      have path := TapeBank.Steps.single (bank I A O constant) data choices _ _ _ _ _ _ _ _ table
      rw [advance_write] at path
      have remainingPath := ih (clock++[false]) next (by dsimp [next];omega)
      have aligned : (bank I A O constant).Steps data choices
          (encoded frame counter (clock++[false]) counterPosition (clock.length+1) (.write initial next)) (remaining+1)
          (encoded frame counter (clock++List.replicate (remaining+1) false) counterPosition (clock.length+(remaining+1))
            (if initial then .read else .advance)) := by
        simpa [List.append_assoc,List.replicate_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using remainingPath
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path.trans (bank I A O constant) aligned

theorem advance_counter {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (counter clock : List Bool) (counterPosition clockPosition : ℕ) :
    (bank I A O constant).Steps data choices (encoded frame counter clock counterPosition clockPosition .advance) 1
      (encoded frame counter clock (counterPosition+1) clockPosition .read) := by
  have path := TapeBank.Steps.read (bank I A O constant) data choices
    (encoded frame counter clock counterPosition clockPosition .advance) .read .right 0 rfl
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) rfl
  convert path using 1
  apply BankConfiguration.ext <;> try rfl
  funext index
  rcases two_index index with rfl | rfl <;> simp [encoded,Move.onInt]

theorem read_steps {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (low high clock : List Bool) :
    (bank I A O constant).Steps data choices (encoded frame (low++high) clock low.length clock.length .read)
      ((constant+3)*high.length+1)
      (encoded frame (low++high) (clock++List.replicate (constant*high.length) false) (low++high).length
        (clock.length+constant*high.length) .rewind) := by
  induction high generalizing low clock with
  | nil =>
      have path := go (O:=O) constant frame data choices (low++[]) clock low.length clock.length .read .rewind (by
        simp [TapeBank.instruction,bank,selected,transition,encoded,counterTape,digitTape])
      simpa using path
  | cons bit rest ih =>
      have start := go (O:=O) constant frame data choices (low++bit::rest) clock low.length clock.length .read (.write false 0) (by
        simp [TapeBank.instruction,bank,selected,transition,encoded,counterTape,digitTape_at])
      have writing := write_steps (O:=O) constant frame data choices (low++bit::rest) clock low.length false 0 constant (by simp)
      have next := advance_counter (O:=O) constant frame data choices (low++bit::rest)
        (clock++List.replicate constant false) low.length (clock.length+constant)
      have tail := ih (low++[bit]) (clock++List.replicate constant false)
      have aligned : (bank I A O constant).Steps data choices
          (encoded frame (low++bit::rest) (clock++List.replicate constant false) (low.length+1) (clock.length+constant) .read)
          ((constant+3)*rest.length+1)
          (encoded frame (low++bit::rest) (clock++List.replicate (constant*(rest.length+1)) false)
            (low++bit::rest).length (clock.length+constant*(rest.length+1)) .rewind) := by
        simpa [List.append_assoc,← List.replicate_add,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail
      have both := ((start.trans (bank I A O constant) writing).trans (bank I A O constant) next).trans (bank I A O constant) aligned
      have time : 1+(constant+1)+1+((constant+3)*rest.length+1)=(constant+3)*(rest.length+1)+1 := by ring
      simpa only [List.length_cons,time] using both

theorem rewind_counter {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (counter clock : List Bool) (counterPosition clockPosition : ℕ) :
    (bank I A O constant).Steps data choices (encoded frame counter clock counterPosition clockPosition .rewind)
      (counterPosition+1) (encoded frame counter clock 0 clockPosition .done) := by
  have path := TapeBank.rewind_steps (bank I A O constant) data choices .rewind .done 0 rfl
    (by intro input auxiliary index origin cell;rfl) counterPosition
    (encoded frame counter clock counterPosition clockPosition .rewind) rfl (by simp [encoded])
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  convert path using 1
  apply BankConfiguration.ext <;> try rfl
  funext index
  rcases two_index index with rfl | rfl <;> simp [encoded]

theorem routine_steps {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (digits : List Bool) :
    (bank I A O constant).Steps data choices (encoded frame digits [] 0 0 (.write true 0))
      (constant+1+((constant+3)*digits.length+1)+(digits.length+1))
      (encoded frame digits (List.replicate (constant*(digits.length+1)) false) 0 (constant*(digits.length+1)) .done) := by
  have initial := write_steps (O:=O) constant frame data choices digits [] 0 true 0 constant (by simp)
  have scanning := read_steps (O:=O) constant frame data choices [] digits (List.replicate constant false)
  have middle : (bank I A O constant).Steps data choices (encoded frame digits (List.replicate constant false) 0 constant .read)
      ((constant+3)*digits.length+1)
      (encoded frame digits (List.replicate (constant*(digits.length+1)) false) digits.length (constant*(digits.length+1)) .rewind) := by
    simpa [← List.replicate_add,Nat.mul_add,Nat.add_comm] using scanning
  have back := rewind_counter (O:=O) constant frame data choices digits (List.replicate (constant*(digits.length+1)) false)
    digits.length (constant*(digits.length+1))
  have first : (bank I A O constant).Steps data choices (encoded frame digits [] 0 0 (.write true 0)) (constant+1)
      (encoded frame digits (List.replicate constant false) 0 constant .read) := by simpa using initial
  exact (first.trans (bank I A O constant) middle).trans (bank I A O constant) back

theorem routine_regionSteps {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (digits : List Bool) :
    (bank I A O constant).RegionSteps data choices ((constant+5)*(digits.length+1))
      (encoded frame digits [] 0 0 (.write true 0))
      (constant+1+((constant+3)*digits.length+1)+(digits.length+1))
      (encoded frame digits (List.replicate (constant*(digits.length+1)) false) 0 (constant*(digits.length+1)) .done) := by
  have initial : (bank I A O constant).Bounded data 0 (encoded frame digits [] 0 0 (.write true 0)) := by
    constructor <;> simp [encoded]
  exact ((routine_steps constant frame data choices digits).inRegion (bank I A O constant) 0 initial).mono
    (bank I A O constant) (by nlinarith)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.LogSeed
