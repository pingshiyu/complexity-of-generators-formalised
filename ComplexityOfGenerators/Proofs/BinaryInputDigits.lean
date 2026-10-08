import ComplexityOfGenerators.Proofs.BinaryInputSteps

/-! The native continuation/digit loop writes exactly one canonical binary
digit per iteration. Its random and transition counts are proved explicitly. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

theorem binary_input_digits (data : InputData Unit Bool) (bits : BitString)
    (family : Bool) (digits : List Bool) (extra : BitString)
    (written : List RecursiveAlphabet) (consumed : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet (.flag family) written consumed c)
    (seed : bits.drop consumed = binaryDigitSeed digits ++ extra) :
    ∃ d, BinaryPrepared program control alphabet (.finish family)
        (written ++ digits.map (fun bit => stackLetter (binaryGlyph bit)))
        (consumed + (2 * digits.length + 1)) d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c (3 * digits.length + 1) =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  induction digits generalizing written consumed c with
  | nil =>
      have stop : bits[consumed]? = some false := by
        change bits[consumed + 0]? = some false
        rw [← List.getElem?_drop, seed]
        rfl
      obtain ⟨d, final, execution⟩ := binary_input_random program control alphabet data bits
        (.flag family) (.finish family) (.digit family) written consumed false c prepared stop rfl
      exact ⟨d, by simpa using final, by simpa using execution⟩
  | cons bit digits ih =>
      have flag : bits[consumed]? = some true := by
        change bits[consumed + 0]? = some true
        rw [← List.getElem?_drop, seed]
        rfl
      have digit : bits[consumed + 1]? = some bit := by
        rw [← List.getElem?_drop, seed]
        rfl
      have rest : bits.drop (consumed + 2) = binaryDigitSeed digits ++ extra := by
        simpa [binaryDigitSeed, List.drop_drop, List.append_assoc] using
          congrArg (fun xs : BitString => xs.drop 2) seed
      obtain ⟨selected, selectedReady, selection⟩ := binary_input_random program control alphabet data bits
        (.flag family) (.finish family) (.digit family) written consumed true c prepared flag rfl
      obtain ⟨read, readReady, reading⟩ := binary_input_random program control alphabet data bits
        (.digit family) (.write family false) (.write family true) written (consumed + 1) bit
        selected (by simpa using selectedReady) digit rfl
      have table : binaryInputInstruction program control alphabet (.write family bit) (read.work read.workHead) =
          .step (binaryInputControl (.flag family)) (some (bootEncode alphabet (stackLetter (binaryGlyph bit))))
            .right .stay .stay .stay none := rfl
      obtain ⟨updated, updatedReady, update⟩ := binary_input_write program control alphabet data bits
        (.write family bit) (.flag family) written (consumed + 2) (stackLetter (binaryGlyph bit))
        read (by cases bit <;> simpa [Nat.add_assoc] using readReady) table
      obtain ⟨d, final, execution⟩ := ih (written ++ [stackLetter (binaryGlyph bit)]) (consumed + 2)
        updated updatedReady rest
      refine ⟨d, ?_, ?_⟩
      · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_succ] using final
      · have first := M.runFrom_add data bits c selected 1 selection (1 + (1 + (3 * digits.length + 1)))
        have second := M.runFrom_add data bits selected read 1 reading (1 + (3 * digits.length + 1))
        have third := M.runFrom_add data bits read updated 1 update (3 * digits.length + 1)
        have clock : 1 + (1 + (1 + (3 * digits.length + 1))) = 3 * (bit :: digits).length + 1 := by
          simp only [List.length_cons]
          omega
        have result := first.trans (second.trans (third.trans execution))
        rw [clock] at result
        exact result

end

end ComplexityOfGenerators
