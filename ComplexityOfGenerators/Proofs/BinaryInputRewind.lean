import ComplexityOfGenerators.Proofs.BinaryInputBootstrap

/-! The sampled stack is rewound to its bottom. The resulting configuration
is related to the actual source Post initialization, rather than to an abstract
or preloaded computation. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

def BinaryRewinding (word : List RecursiveAlphabet) (r : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet)) : Prop :=
  c.state = binaryInputControl .rewind ∧ c.workHead = (r : ℤ) - 1 ∧
    c.work = bootMemory alphabet word word.length ∧ c.output = []

theorem binary_input_rewind (data : InputData Unit Bool) (bits : BitString)
    (word : List RecursiveAlphabet) (r : ℕ) (bound : r ≤ word.length + 1)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryRewinding program control alphabet word r c) :
    ∃ d, PostRelated (binaryInputSimulator program control alphabet) (TM0.init word) d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c (r + 1) =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  induction r generalizing c with
  | zero =>
      obtain ⟨state, head, memory, output⟩ := prepared
      have marker : c.work c.workHead = some (Fin.last symbols) := by simp [memory, head, bootMemory]
      let d := M.stepConfiguration data c (binaryInputControl (.run (control default)))
        none .right .stay .stay .stay none
      have table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
          .step (binaryInputControl (.run (control default))) none .right .stay .stay .stay none := by
        simp [M, binaryInputMachine, state, binaryInputInstruction, marker]
      have live := M.observe_step data bits c _ _ _ _ _ _ _ table
      have step := M.next_step data bits c _ _ _ _ _ _ _ table
      refine ⟨d, ⟨rfl, output, ?_⟩, M.runFrom_shift data bits c d live step 0⟩
      intro i
      change bootDecode alphabet (c.work ((c.workHead + 1) + i)) = _
      have position : (c.workHead + 1) + i = i := by rw [head]; omega
      rw [position, memory]
      exact bootMemory_input alphabet word i
  | succ r ih =>
      obtain ⟨state, head, memory, output⟩ := prepared
      have position : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by omega
      have unmarked : c.work c.workHead ≠ some (Fin.last symbols) := by
        rw [memory, head, position]
        by_cases inside : r < word.length
        · exact bootMemory_not_marker alphabet word r inside
        · have atEnd : r = word.length := by omega
          subst r
          have notMarker : (word.length : ℤ) ≠ -1 := by omega
          simp [bootMemory, notMarker]
      let next := M.stepConfiguration data c (binaryInputControl .rewind) none .left .stay .stay .stay none
      have table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
          .step (binaryInputControl .rewind) none .left .stay .stay .stay none := by
        simp [M, binaryInputMachine, state, binaryInputInstruction, unmarked]
      have live := M.observe_step data bits c _ _ _ _ _ _ _ table
      have step := M.next_step data bits c _ _ _ _ _ _ _ table
      have nextReady : BinaryRewinding program control alphabet word r next := by
        refine ⟨rfl, ?_, memory, output⟩
        change c.workHead - 1 = (r : ℤ) - 1
        rw [head, position]
      obtain ⟨d, final, execution⟩ := ih (by omega) next nextReady
      exact ⟨d, final, (M.runFrom_shift data bits c next live step (r + 1)).trans execution⟩

end

end ComplexityOfGenerators
