import ComplexityOfGenerators.Proofs.BinaryInputRewind

/-! Complete native initialization on the concrete seeds witnessing full
support of the candidate and clock. The execution starts with blank work tape
and ends in the compiled program's actual initial Post configuration. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

theorem binary_input_bootstrap_num (data : InputData Unit Bool) (candidate clock : Num)
    (extra : BitString) :
    ∃ t d, PostRelated (binaryInputSimulator program control alphabet)
        (TM0.init (recursiveInput [(clock : ℕ), (candidate : ℕ)])) d ∧
      (binaryInputMachine program control alphabet).run data
        (numSeed candidate ++ numSeed clock ++ extra) t =
        (binaryInputMachine program control alphabet).observe data
          (numSeed candidate ++ numSeed clock ++ extra) d := by
  let M := binaryInputMachine program control alphabet
  let bits := numSeed candidate ++ numSeed clock ++ extra
  let word := recursiveInput [(clock : ℕ), (candidate : ℕ)]
  obtain ⟨initial, initialReady, initialRun⟩ := binary_input_initial program control alphabet data bits
  obtain ⟨pairTime, sampled, sampledReady, pairRun⟩ := binary_input_pair program control alphabet data bits
    candidate clock extra 0 initial initialReady (by simp [bits])
  obtain ⟨rewinding, rewindingReady, skip⟩ := binary_input_skip program control alphabet data bits
    (.finish true) .rewind word ((numSeed candidate).length + (numSeed clock).length)
    sampled (by simpa using sampledReady) rfl
  have rewindReady : BinaryRewinding program control alphabet word (word.length + 1) rewinding := by
    obtain ⟨state, head, random, memory, output⟩ := rewindingReady
    refine ⟨state, ?_, memory, output⟩
    rw [head]
    omega
  obtain ⟨d, final, rewind⟩ := binary_input_rewind program control alphabet data bits word
    (word.length + 1) (by omega) rewinding rewindReady
  refine ⟨3 + (pairTime + (1 + (word.length + 1 + 1))), d, final, ?_⟩
  rw [← M.runFrom_initial] at initialRun ⊢
  have first := M.runFrom_add data bits M.initialConfiguration initial 3 initialRun
    (pairTime + (1 + (word.length + 1 + 1)))
  have second := M.runFrom_add data bits initial sampled pairTime pairRun (1 + (word.length + 1 + 1))
  have third := M.runFrom_add data bits sampled rewinding 1 skip (word.length + 1 + 1)
  exact first.trans (second.trans (third.trans rewind))

/-- Every natural clock/candidate pair has an explicit native initialization
seed. Additional randomness is ignored until the compiled program starts. -/
theorem binary_input_bootstrap (data : InputData Unit Bool) (candidate clock : ℕ)
    (extra : BitString) :
    ∃ t d, PostRelated (binaryInputSimulator program control alphabet)
        (TM0.init (recursiveInput [clock, candidate])) d ∧
      (binaryInputMachine program control alphabet).run data
        (binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra) t =
        (binaryInputMachine program control alphabet).observe data
          (binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra) d := by
  have initialized := binary_input_bootstrap_num program control alphabet data (candidate : Num) (clock : Num) extra
  norm_cast at initialized

end

end ComplexityOfGenerators
