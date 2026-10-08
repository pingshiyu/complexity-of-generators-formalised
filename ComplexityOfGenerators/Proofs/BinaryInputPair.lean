import ComplexityOfGenerators.Proofs.BinaryInputNumber

/-! The two native number-sampling loops prepare exactly the library's input
stack for `[clock, candidate]`, including zero values and all delimiters. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

theorem binary_input_pair (data : InputData Unit Bool) (bits : BitString)
    (candidate clock : Num) (extra : BitString) (consumed : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet (.select false) [stackBottom .cons] consumed c)
    (seed : bits.drop consumed = numSeed candidate ++ numSeed clock ++ extra) :
    ∃ t d, BinaryPrepared program control alphabet (.finish true)
        (recursiveInput [(clock : ℕ), (candidate : ℕ)])
        (consumed + (numSeed candidate).length + (numSeed clock).length) d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c t =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  obtain ⟨firstTime, first, firstReady, firstRun⟩ := binary_input_number program control alphabet
    data bits false candidate (numSeed clock ++ extra) [stackBottom .cons] consumed c prepared
    (by simpa [List.append_assoc] using seed)
  have nextSeed : bits.drop (consumed + (numSeed candidate).length) = numSeed clock ++ extra := by
    simpa [List.drop_drop, List.append_assoc] using
      congrArg (fun xs : BitString => xs.drop (numSeed candidate).length) seed
  obtain ⟨selected, selectedReady, selection⟩ := binary_input_write program control alphabet data bits
    (.finish false) (.select true)
    ([stackBottom .cons] ++ (PartrecToTM2.trNat (candidate : ℕ)).reverse.map stackLetter)
    (consumed + (numSeed candidate).length) (stackLetter .cons) first firstReady rfl
  obtain ⟨secondTime, final, finalReady, secondRun⟩ := binary_input_number program control alphabet
    data bits true clock extra
    (([stackBottom .cons] ++ (PartrecToTM2.trNat (candidate : ℕ)).reverse.map stackLetter) ++ [stackLetter .cons])
    (consumed + (numSeed candidate).length) selected selectedReady nextSeed
  refine ⟨firstTime + (1 + secondTime), final, ?_, ?_⟩
  · rw [recursiveInput_pair]
    simpa [List.append_assoc] using finalReady
  · have firstPart := M.runFrom_add data bits c first firstTime firstRun (1 + secondTime)
    have secondPart := M.runFrom_add data bits first selected 1 selection secondTime
    exact firstPart.trans (secondPart.trans secondRun)

end

end ComplexityOfGenerators
