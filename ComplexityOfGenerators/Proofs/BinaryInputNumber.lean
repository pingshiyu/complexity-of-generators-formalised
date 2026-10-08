import ComplexityOfGenerators.Proofs.BinaryInputDigits

/-! Complete execution of one sampled number in the native input routine.
The written cells use exactly Mathlib's canonical binary stack representation. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

theorem binary_input_number (data : InputData Unit Bool) (bits : BitString)
    (family : Bool) (n : Num) (extra : BitString)
    (written : List RecursiveAlphabet) (consumed : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet (.select family) written consumed c)
    (seed : bits.drop consumed = numSeed n ++ extra) :
    ∃ t d, BinaryPrepared program control alphabet (.finish family)
        (written ++ (PartrecToTM2.trNat (n : ℕ)).reverse.map stackLetter)
        (consumed + (numSeed n).length) d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c t =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  cases n with
  | zero =>
      have stop : bits[consumed]? = some false := by
        change bits[consumed + 0]? = some false
        rw [← List.getElem?_drop, seed]
        rfl
      obtain ⟨d, final, execution⟩ := binary_input_random program control alphabet data bits
        (.select family) (.finish family) (.write family true) written consumed false c prepared stop rfl
      exact ⟨1, d, by simpa [numSeed] using final, execution⟩
  | pos n =>
      have positive : bits[consumed]? = some true := by
        change bits[consumed + 0]? = some true
        rw [← List.getElem?_drop, seed]
        rfl
      have rest : bits.drop (consumed + 1) = binaryDigitSeed (positiveDigits n) ++ extra := by
        simpa [numSeed, List.drop_drop] using congrArg (fun xs : BitString => xs.drop 1) seed
      obtain ⟨selected, selectedReady, selection⟩ := binary_input_random program control alphabet data bits
        (.select family) (.finish family) (.write family true) written consumed true c prepared positive rfl
      obtain ⟨updated, updatedReady, update⟩ := binary_input_write program control alphabet data bits
        (.write family true) (.flag family) written (consumed + 1) (stackLetter .bit1)
        selected (by simpa using selectedReady) rfl
      obtain ⟨d, final, execution⟩ := binary_input_digits program control alphabet data bits family
        (positiveDigits n) extra (written ++ [stackLetter .bit1]) (consumed + 1) updated updatedReady rest
      have encoding : (PartrecToTM2.trNat (n : ℕ)).reverse =
          .bit1 :: (positiveDigits n).map binaryGlyph := by
        simpa [binaryDigitsValue_positiveDigits] using trNat_binaryDigitsValue (positiveDigits n)
      refine ⟨1 + (1 + (3 * (positiveDigits n).length + 1)), d, ?_, ?_⟩
      · change BinaryPrepared program control alphabet (.finish family)
          (written ++ (PartrecToTM2.trNat (n : ℕ)).reverse.map stackLetter)
          (consumed + (numSeed (.pos n)).length) d
        rw [encoding]
        simpa [numSeed, binaryDigitSeed, List.length_flatMap, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm,
          List.map_map, Function.comp_def] using final
      · have first := M.runFrom_add data bits c selected 1 selection (1 + (3 * (positiveDigits n).length + 1))
        have second := M.runFrom_add data bits selected updated 1 update (3 * (positiveDigits n).length + 1)
        exact first.trans (second.trans execution)

end

end ComplexityOfGenerators
