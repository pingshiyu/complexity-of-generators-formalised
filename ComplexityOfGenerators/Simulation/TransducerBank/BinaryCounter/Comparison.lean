import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.ComparisonWords
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Tape
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import ComplexityOfGenerators.Simulation.TransducerBank.PassiveContext

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Comparison

set_option backward.isDefEq.respectTransparency false

inductive Control | scan (less : Bool) | rewind (less : Bool) | done (less : Bool)
  deriving DecidableEq,Fintype

def transition {I A O : Type} {tracks : ℕ} (left right : Fin tracks) (state : Control)
    (_ : Option I) (_ : Option A) (_ : Option Unit) (origin : Bool) (cell : Fin tracks→Option Bool) :
    BankInstruction Control (Fin tracks→Option Bool) O :=
  match state with
  | .done _ => .accept
  | .scan prior =>
      if cell left=none ∧ cell right=none then .step (.rewind prior) cell .stay .stay .stay .stay none
      else .step (.scan (update prior (cell left,cell right))) cell .right .stay .stay .stay none
  | .rewind less => .step (if origin then .done less else .rewind less) cell
      (if origin then .stay else .left) .stay .stay .stay none

def bank (I A O : Type) {tracks : ℕ} (left right : Fin tracks) : TapeBank I A O Control (Fin tracks→Option Bool) 1 where
  initial := .scan false
  blank := fun _ => none
  select := fun _ => 0
  transition := transition left right

def cellTape (cells : List Cell) (position : ℤ) : Cell :=
  if 0≤position then cells[position.toNat]?.getD (none,none) else (none,none)

def memory {tracks : ℕ} (left right : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (cells : List Cell) (position : ℤ) : Fin tracks→Option Bool :=
  Function.update (Function.update (other position) left (cellTape cells position).1) right (cellTape cells position).2

def encoded {O : Type} {tracks : ℕ} (left right : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (cells : List Cell) (position : ℕ) (state : Control) : BankConfiguration O Control (Fin tracks→Option Bool) 1 :=
  ⟨state,0,0,0,0,[],fun _ => position,fun _ => memory left right other cells⟩

theorem cellTape_at (low high : List Cell) : cellTape (low++high) low.length=high.head?.getD (none,none) := by
  cases high <;> simp [cellTape,List.getElem?_append_right]

theorem memory_left {tracks : ℕ} (left right : Fin tracks) (different : left≠right)
    (other : ℤ→Fin tracks→Option Bool) (cells : List Cell) (position : ℤ) :
    memory left right other cells position left=(cellTape cells position).1 := by
  simp [memory,Function.update_of_ne different]

theorem memory_right {tracks : ℕ} (left right : Fin tracks)
    (other : ℤ→Fin tracks→Option Bool) (cells : List Cell) (position : ℤ) :
    memory left right other cells position right=(cellTape cells position).2 := by simp [memory]

theorem scan_steps {I A O : Type} {tracks : ℕ} (left right : Fin tracks) (different : left≠right)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString)
    (low high : List Cell) (nonblank : ∀ cell∈high,cell≠(none,none)) (prior : Bool) :
    (bank I A O left right).Steps data choices (encoded left right other (low++high) low.length (.scan prior))
      (high.length+1) (encoded left right other (low++high) (low++high).length (.rewind (scan high prior))) := by
  induction high generalizing low prior with
  | nil =>
      have table : (bank I A O left right).instruction data (encoded left right other (low++[]) low.length (.scan prior))=
          .step (.rewind prior) (memory left right other (low++[]) low.length) .stay .stay .stay .stay none := by
        simp [TapeBank.instruction,bank,transition,encoded,memory_left left right different,memory_right,cellTape]
      have path := TapeBank.Steps.go (bank I A O left right) data choices _ (.rewind prior)
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) table
      simpa [encoded,scan] using path
  | cons cell rest ih =>
      have present : cell.1≠none ∨ cell.2≠none := by
        have good := nonblank cell (by simp)
        by_cases first : cell.1=none
        · right
          intro second
          exact good (Prod.ext first second)
        · exact Or.inl first
      have nonempty : ¬(cell.1=none ∧ cell.2=none) := by
        intro empty
        rcases present with present | present
        · exact present empty.1
        · exact present empty.2
      have table : (bank I A O left right).instruction data (encoded left right other (low++cell::rest) low.length (.scan prior))=
          .step (.scan (update prior cell)) (memory left right other (low++cell::rest) low.length) .right .stay .stay .stay none := by
        simp [TapeBank.instruction,bank,transition,encoded,memory_left left right different,memory_right,cellTape_at,nonempty]
      have path := TapeBank.Steps.read (bank I A O left right) data choices
        (encoded left right other (low++cell::rest) low.length (.scan prior)) (.scan (update prior cell)) .right 0 rfl
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) table
      have advanced : (bank I A O left right).Steps data choices
          (encoded left right other (low++cell::rest) low.length (.scan prior)) 1
          (encoded left right other (low++cell::rest) (low.length+1) (.scan (update prior cell))) := by
        convert path using 1
        apply BankConfiguration.ext <;> try rfl
        funext index
        rw [one_index index]
        simp [encoded,Move.onInt]
      have remaining := ih (low++[cell]) (by intro value member;exact nonblank value (by simp [member])) (update prior cell)
      have aligned : (bank I A O left right).Steps data choices
          (encoded left right other (low++cell::rest) (low.length+1) (.scan (update prior cell))) (rest.length+1)
          (encoded left right other (low++cell::rest) (low++cell::rest).length (.rewind (scan rest (update prior cell)))) := by
        simpa [List.append_assoc] using remaining
      simpa [scan,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using advanced.trans (bank I A O left right) aligned

theorem routine_steps {I A O : Type} {tracks : ℕ} (left right : Fin tracks) (different : left≠right)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString) (first second : List Bool) :
    (bank I A O left right).Steps data choices (encoded left right other (paired first second) 0 (.scan false))
      (2*(max first.length second.length+1))
      (encoded left right other (paired first second) 0 (.done (decide (FixedBitBlocks.decode first<FixedBitBlocks.decode second)))) := by
  have path := scan_steps (O:=O) left right different other data choices [] (paired first second) (paired_nonblank first second) false
  have result : scan (paired first second) false=decide (FixedBitBlocks.decode first<FixedBitBlocks.decode second) := by
    rw [scan_paired]
    split_ifs with same
    · simp [same]
    · rfl
  let answer := decide (FixedBitBlocks.decode first<FixedBitBlocks.decode second)
  have firstPath : (bank I A O left right).Steps data choices (encoded left right other (paired first second) 0 (.scan false))
      (max first.length second.length+1)
      (encoded left right other (paired first second) (paired first second).length (.rewind answer)) := by
    simpa [result,paired_length,answer] using path
  have back := TapeBank.rewind_steps (bank I A O left right) data choices (.rewind answer) (.done answer) 0 rfl
    (by intro input auxiliary index origin cell;rfl) (paired first second).length
    (encoded left right other (paired first second) (paired first second).length (.rewind answer)) rfl rfl
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have aligned : (bank I A O left right).Steps data choices
      (encoded left right other (paired first second) (paired first second).length (.rewind answer))
      ((paired first second).length+1) (encoded left right other (paired first second) 0 (.done answer)) := by
    convert back using 1
    apply BankConfiguration.ext <;> try rfl
    funext index
    rw [one_index index]
    rfl
  have both := firstPath.trans (bank I A O left right) aligned
  have time : max first.length second.length+1+(max first.length second.length+1)=
      2*(max first.length second.length+1) := by omega
  simpa only [paired_length,time,answer] using both

theorem routine_regionSteps {I A O : Type} {tracks : ℕ} (left right : Fin tracks) (different : left≠right)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString)
    (first second : List Bool) (canonicalFirst : Canonical first) (canonicalSecond : Canonical second)
    (bound : ℕ) (firstSmall : FixedBitBlocks.decode first≤bound) (secondSmall : FixedBitBlocks.decode second≤bound) :
    (bank I A O left right).RegionSteps data choices (2*Nat.clog 2 (bound+1)+2)
      (encoded left right other (paired first second) 0 (.scan false)) (2*(max first.length second.length+1))
      (encoded left right other (paired first second) 0 (.done (decide (FixedBitBlocks.decode first<FixedBitBlocks.decode second)))) := by
  have firstLength := canonical_length_bound first canonicalFirst (Nat.clog 2 (bound+1)) (by
    have power := Nat.le_pow_clog (by decide : 1<2) (bound+1);omega)
  have secondLength := canonical_length_bound second canonicalSecond (Nat.clog 2 (bound+1)) (by
    have power := Nat.le_pow_clog (by decide : 1<2) (bound+1);omega)
  have initial : (bank I A O left right).Bounded data 0 (encoded left right other (paired first second) 0 (.scan false)) := by
    constructor <;> simp [encoded]
  exact ((routine_steps left right different other data choices first second).inRegion (bank I A O left right) 0 initial).mono
    (bank I A O left right) (by omega)

theorem cellTape_paired (first second : List Bool) (position : ℤ) :
    cellTape (paired first second) position=(digitTape first position,digitTape second position) := by
  by_cases positive : 0≤position
  · simpa [cellTape,digitTape,positive] using paired_lookup first second position.toNat
  · simp [cellTape,digitTape,positive]

theorem workOnly (I A O : Type) {tracks : ℕ} (left right : Fin tracks) : (bank I A O left right).WorkOnly := by
  constructor
  · intros;rfl
  · intro state input auxiliary index origin cell
    cases state with
    | done less => trivial
    | rewind less => simp [bank,transition]
    | scan prior =>
        by_cases empty : cell left=none ∧ cell right=none <;> simp [bank,transition,empty]

theorem routine_framed {I A O : Type} {tracks : ℕ} (left right : Fin tracks) (different : left≠right)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString)
    (context : Context O) (valid : context.Valid data)
    (first second : List Bool) (canonicalFirst : Canonical first) (canonicalSecond : Canonical second)
    (bound : ℕ) (firstSmall : FixedBitBlocks.decode first≤bound) (secondSmall : FixedBitBlocks.decode second≤bound) :
    (bank I A O left right).RegionSteps data choices (2*Nat.clog 2 (bound+1)+2)
      (context.frame (encoded left right other (paired first second) 0 (.scan false)))
      (2*(max first.length second.length+1))
      (context.frame (encoded left right other (paired first second) 0
        (.done (decide (FixedBitBlocks.decode first<FixedBitBlocks.decode second))))) := by
  exact Context.regionSteps_frame (bank I A O left right) (workOnly I A O left right) data choices context valid
    (routine_regionSteps left right different other data choices first second canonicalFirst canonicalSecond bound firstSmall secondSmall)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Comparison
