import ComplexityOfGenerators.Simulation.WordInput

/-! Properties of Mathlib's binary stack encoding needed by the native output
routine. Its finite dictionary contains the encodings of the output alphabet;
distinct letters must not share a binary code. -/

namespace ComplexityOfGenerators.Simulation

open Turing Encodable

def readBinary : List PartrecToTM2.Γ' → ℕ
  | [] => 0
  | .bit0 :: tail => 2 * readBinary tail
  | .bit1 :: tail => 2 * readBinary tail + 1
  | _ :: _ => 0

theorem readBinary_trPosNum (n : PosNum) :
    readBinary (PartrecToTM2.trPosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [PartrecToTM2.trPosNum, readBinary, ih, two_mul]
  | bit1 n ih => simp [PartrecToTM2.trPosNum, readBinary, ih, two_mul]

theorem readBinary_trNum (n : Num) : readBinary (PartrecToTM2.trNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos n => exact readBinary_trPosNum n

theorem readBinary_trNat (n : ℕ) : readBinary (PartrecToTM2.trNat n) = n := by
  rw [PartrecToTM2.trNat, readBinary_trNum]
  norm_cast

theorem trNat_injective : Function.Injective PartrecToTM2.trNat := by
  intro m n equal
  simpa only [readBinary_trNat] using congrArg readBinary equal

theorem trPosNum_bits (n : PosNum) :
    ∀ symbol ∈ PartrecToTM2.trPosNum n, symbol = .bit0 ∨ symbol = .bit1 := by
  induction n with
  | one => simp [PartrecToTM2.trPosNum]
  | bit0 n ih => simpa [PartrecToTM2.trPosNum] using ih
  | bit1 n ih => simpa [PartrecToTM2.trPosNum] using ih

theorem trNat_bits (n : ℕ) :
    ∀ symbol ∈ PartrecToTM2.trNat n, symbol = .bit0 ∨ symbol = .bit1 := by
  unfold PartrecToTM2.trNat
  cases (n : Num) with
  | zero => simp [PartrecToTM2.trNum]
  | pos p => exact trPosNum_bits p

/-- A letter is scanned in big-endian order, starting at the stack bottom. -/
def outputBlock {α : Type} [Encodable α] (letter : α) : List PartrecToTM2.Γ' :=
  (PartrecToTM2.trNat (encode letter)).reverse

theorem outputBlock_injective {α : Type} [Encodable α] :
    Function.Injective (outputBlock (α := α)) := by
  intro a b equal
  apply encode_injective
  apply trNat_injective
  simpa [outputBlock] using congrArg List.reverse equal

theorem outputBlock_bits {α : Type} [Encodable α] (letter : α) :
    ∀ symbol ∈ outputBlock letter, symbol = .bit0 ∨ symbol = .bit1 := by
  intro symbol member
  exact trNat_bits _ symbol (List.mem_reverse.mp member)

def outputCells {α : Type} [Encodable α] (word : List α) : List PartrecToTM2.Γ' :=
  word.flatMap (fun letter => .cons :: outputBlock letter)

/-- Decoding the scalar word code into reversed letters makes the library's
reversed main stack readable in the original word order. -/
theorem outputCells_encoding {α : Type} [Encodable α] (word : List α) :
    (PartrecToTM2.trList (word.reverse.map encode)).reverse = outputCells word := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        trList_append, PartrecToTM2.trList, List.reverse_append, List.reverse_cons,
        List.reverse_nil, ih, outputCells, List.flatMap_cons]
      rfl

end ComplexityOfGenerators.Simulation
