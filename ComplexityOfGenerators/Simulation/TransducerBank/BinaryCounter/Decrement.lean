import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.DecrementWords
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Tape
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Decrement

set_option backward.isDefEq.respectTransparency false

inductive Control | borrow | inspect | erase | rewind | done
  deriving DecidableEq,Fintype

def transition {I A O : Type} (state : Control) (_ : Option I) (_ : Option A) (_ : Option Unit)
    (origin : Bool) (cell : Option Bool) : BankInstruction Control (Option Bool) O :=
  match state with
  | .done => .accept
  | .borrow => match cell with
      | none => .step .rewind none .stay .stay .stay .stay none
      | some false => .step .borrow (some true) .right .stay .stay .stay none
      | some true => .step .inspect (some false) .right .stay .stay .stay none
  | .inspect => .step (if cell.isNone then .erase else .rewind) cell .left .stay .stay .stay none
  | .erase => .step .rewind none .stay .stay .stay .stay none
  | .rewind => .step (if origin then .done else .rewind) cell
      (if origin then .stay else .left) .stay .stay .stay none

def bank (I A O : Type) : TapeBank I A O Control (Option Bool) 1 where
  initial := .borrow
  blank := none
  select := fun _ => 0
  transition := transition

def encoded {O : Type} (bits : List Bool) (position : ℕ) (state : Control) :
    BankConfiguration O Control (Option Bool) 1 :=
  ⟨state,0,0,0,0,[],fun _ => position,fun _ => digitTape bits⟩

theorem digitTape_erase_last (low : List Bool) (bit : Bool) :
    Function.update (digitTape (low++[bit])) (low.length : ℤ) none=digitTape low := by
  funext position
  by_cases same : position=(low.length : ℤ)
  · subst position
    simp [digitTape]
  · rw [Function.update_of_ne same]
    by_cases nonnegative : 0≤position
    · simp only [digitTape,ite_eq_left nonnegative]
      by_cases before : position.toNat<low.length
      · exact List.getElem?_append_left before
      · have later : low.length<position.toNat := by omega
        rw [List.getElem?_eq_none (by omega : low.length≤position.toNat),
          List.getElem?_eq_none (by simp;omega : (low++[bit]).length≤position.toNat)]
    · simp [digitTape,nonnegative]

theorem advance_write {I A O : Type} (data : InputData I A) (low high : List Bool)
    (state next : Control) (bit : Bool) (work : Move) (position : ℕ)
    (moved : work.onInt (low.length : ℤ)=(position : ℤ)) :
    (bank I A O).advance data (encoded (low++high) low.length state) next (some bit)
      work .stay .stay .stay none=encoded (low++bit::high.tail) position next := by
  apply BankConfiguration.ext <;> try rfl
  all_goals try {simp [TapeBank.advance,encoded,Move.onInput]}
  · funext index
    rw [one_index index]
    simpa [TapeBank.advance,encoded,bank] using moved
  · funext index
    rw [one_index index]
    simpa [TapeBank.advance,encoded,bank] using digitTape_write low high bit

theorem advance_erase {I A O : Type} (data : InputData I A) (low : List Bool) :
    (bank I A O).advance data (encoded (low++[false]) low.length .erase) .rewind none
      .stay .stay .stay .stay none=encoded low low.length .rewind := by
  apply BankConfiguration.ext <;> try rfl
  all_goals try {simp [TapeBank.advance,encoded,Move.onInput,Move.onInt,bank,Function.update_eq_self]}
  funext index
  rw [one_index index]
  simpa [TapeBank.advance,encoded,bank] using digitTape_erase_last low false

theorem read_left {I A O : Type} (data : InputData I A) (choices : BitString)
    (bits : List Bool) (position : ℕ) (next : Control)
    (table : (bank I A O).instruction data (encoded bits (position+1) .inspect)=
      .step next (digitTape bits (position+1)) .left .stay .stay .stay none) :
    (bank I A O).Steps data choices (encoded bits (position+1) .inspect) 1 (encoded bits position next) := by
  have path := TapeBank.Steps.read (bank I A O) data choices (encoded bits (position+1) .inspect)
    next .left 0 rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) table
  convert path using 1
  apply BankConfiguration.ext <;> try rfl
  funext index
  rw [one_index index]
  simp [encoded,Move.onInt]

/-- The borrow pass trims the high zero digit, retaining canonical binary
notation and leaving the work head at the last changed digit. -/
theorem borrow_steps {I A O : Type} (data : InputData I A) (choices : BitString)
    (low high : List Bool) (canonical : Canonical high) :
    ∃ time position, time≤high.length+3 ∧ position≤high.length ∧
      (bank I A O).Steps data choices (encoded (low++high) low.length .borrow) time
        (encoded (low++decrement high) (low.length+position) .rewind) := by
  induction high generalizing low with
  | nil =>
      have table : (bank I A O).instruction data (encoded (low++[]) low.length .borrow)=
          .step .rewind none .stay .stay .stay .stay none := by
        simp [TapeBank.instruction,bank,transition,encoded,digitTape]
      have path := TapeBank.Steps.go (bank I A O) data choices (encoded (low++[]) low.length .borrow)
        .rewind (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (by simpa [encoded,digitTape] using table)
      exact ⟨1,0,by simp,by simp,by simpa [decrement,encoded] using path⟩
  | cons first rest ih =>
      cases first with
      | false =>
          have table : (bank I A O).instruction data (encoded (low++false::rest) low.length .borrow)=
              .step .borrow (some true) .right .stay .stay .stay none := by
            simp [TapeBank.instruction,bank,transition,encoded,digitTape_at]
          have path := TapeBank.Steps.single (bank I A O) data choices _ _ _ _ _ _ _ _ table
          rw [advance_write data low (false::rest) .borrow .borrow true .right (low.length+1)
            (by simp [Move.onInt])] at path
          obtain ⟨time,position,budget,distance,tail⟩ := ih (low++[true]) (canonical_tail canonical)
          have aligned : (bank I A O).Steps data choices (encoded (low++true::rest) (low.length+1) .borrow) time
              (encoded (low++true::decrement rest) (low.length+1+position) .rewind) := by
            simpa [List.append_assoc] using tail
          exact ⟨1+time,position+1,by simp at *;omega,by simp at *;omega,
            by simpa [decrement,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path.trans (bank I A O) aligned⟩
      | true =>
          have table : (bank I A O).instruction data (encoded (low++true::rest) low.length .borrow)=
              .step .inspect (some false) .right .stay .stay .stay none := by
            simp [TapeBank.instruction,bank,transition,encoded,digitTape_at]
          have path := TapeBank.Steps.single (bank I A O) data choices _ _ _ _ _ _ _ _ table
          rw [advance_write data low (true::rest) .borrow .inspect false .right (low.length+1)
            (by simp [Move.onInt])] at path
          cases rest with
          | nil =>
              have back : (bank I A O).Steps data choices (encoded (low++[false]) (low.length+1) .inspect) 1
                  (encoded (low++[false]) low.length .erase) := by
                apply read_left
                simp [TapeBank.instruction,bank,transition,encoded,digitTape]
              have eraseTable : (bank I A O).instruction data (encoded (low++[false]) low.length .erase)=
                  .step .rewind none .stay .stay .stay .stay none := rfl
              have erase := TapeBank.Steps.single (bank I A O) data choices _ _ _ _ _ _ _ _ eraseTable
              rw [advance_erase] at erase
              exact ⟨3,0,by simp,by simp,by simpa [decrement] using (path.trans (bank I A O) back).trans (bank I A O) erase⟩
          | cons next rest =>
              have back : (bank I A O).Steps data choices (encoded (low++false::next::rest) (low.length+1) .inspect) 1
                  (encoded (low++false::next::rest) low.length .rewind) := by
                apply read_left
                simp [TapeBank.instruction,bank,transition,encoded,digitTape,List.getElem?_append_right] <;> omega
              exact ⟨2,0,by simp,by simp,by simpa [decrement] using path.trans (bank I A O) back⟩

theorem decrement_steps {I A O : Type} (data : InputData I A) (choices : BitString)
    (bits : List Bool) (canonical : Canonical bits) :
    ∃ time, time≤2*bits.length+4 ∧ (bank I A O).Steps data choices (encoded bits 0 .borrow) time
      (encoded (decrement bits) 0 .done) := by
  obtain ⟨time,position,budget,distance,path⟩ := borrow_steps (O:=O) data choices [] bits canonical
  have back := TapeBank.rewind_steps (bank I A O) data choices .rewind .done 0 rfl
    (by intro input auxiliary index origin cell;rfl) position (encoded (decrement bits) position .rewind)
    rfl rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have aligned : (bank I A O).Steps data choices (encoded (decrement bits) position .rewind) (position+1)
      (encoded (decrement bits) 0 .done) := by
    convert back using 1
    apply BankConfiguration.ext <;> try rfl
    funext index
    rw [one_index index]
    rfl
  refine ⟨time+(position+1),by omega,?_⟩
  have first : (bank I A O).Steps data choices (encoded bits 0 .borrow) time
      (encoded (decrement bits) position .rewind) := by simpa using path
  exact first.trans (bank I A O) aligned

theorem decrement_regionSteps {I A O : Type} (data : InputData I A) (choices : BitString)
    (bits : List Bool) (canonical : Canonical bits) (bound : ℕ) (value : FixedBitBlocks.decode bits≤bound) :
    ∃ time, (bank I A O).RegionSteps data choices (2*Nat.clog 2 (bound+1)+4) (encoded bits 0 .borrow) time
      (encoded (decrement bits) 0 .done) := by
  obtain ⟨time,budget,path⟩ := decrement_steps (O:=O) data choices bits canonical
  have digits := canonical_length_bound bits canonical (Nat.clog 2 (bound+1)) (by
    have power := Nat.le_pow_clog (by decide : 1<2) (bound+1)
    omega)
  have initial : (bank I A O).Bounded data 0 (encoded bits 0 .borrow) := by constructor <;> simp [encoded]
  exact ⟨time,(path.inRegion (bank I A O) 0 initial).mono (bank I A O) (by omega)⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Decrement
