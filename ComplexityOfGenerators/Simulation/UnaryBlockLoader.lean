import ComplexityOfGenerators.Simulation.UnaryInput
import ComplexityOfGenerators.Simulation.BlockBootstrap
import ComplexityOfGenerators.Foundations.ResourceBounds

/-!
# Loading a block expansion of the physical unary index

The loader reads the original family index one cell at a time, expands each
cell into a fixed block on the initially blank work tape, and rewinds before
entering a finite Post program. Both the loaded tape and the exact number of
native transitions are proved. Affine index expansion is a special case.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

def unaryBlockMachine (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks Unit Γ) : Machine Unit Bool Unit :=
  unarySwapMachine (blockMachine program control alphabet blocks)

def unaryBlockSimulator (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks Unit Γ) : PostSimulator program Unit where
  machine := unaryBlockMachine program control alphabet blocks
  control := (blockSimulator program control alphabet blocks).control
  encode := bootEncode alphabet
  decode := bootDecode alphabet
  writeCorrect := bootDecode_encode alphabet
  transitionCorrect := by
    intro q input auxiliary index work
    change unarySwapInstruction (blockMachine program control alphabet blocks)
      ((blockSimulator program control alphabet blocks).machine.transition
        ((blockSimulator program control alphabet blocks).control q)
        index auxiliary input work) = _
    rw [(blockSimulator program control alphabet blocks).transitionCorrect]
    simp only [blockSimulator]
    cases program q (bootDecode alphabet work) with
    | none => rfl
    | some action => rcases action with ⟨q, action⟩; cases action <;> rfl

omit [Fintype Γ] in
/-- The prepared tape is exactly the chosen block expansion of the unary
index. The bound includes all loading, end-marker, and rewind transitions. -/
theorem unaryBlock_bootstrap (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks Unit Γ) (n : ℕ) (bits : BitString) :
    ∃ ready, PostRelated (unaryBlockSimulator program control alphabet blocks)
        (TM0.init (blocks.word (List.replicate n ()))) ready ∧
      (unaryBlockMachine program control alphabet blocks).run (generatorData n) bits
          (2 * (blocks.word (List.replicate n ())).length + 2 * n + 5) =
        (unaryBlockMachine program control alphabet blocks).observe (generatorData n) bits ready := by
  obtain ⟨ready, related, execution⟩ :=
    block_bootstrap program control alphabet blocks (List.replicate n ()) bits
  change Configuration (blockMachine program control alphabet blocks) at ready
  refine ⟨unarySwapConfiguration (blockMachine program control alphabet blocks) ready, related, ?_⟩
  change (unarySwapMachine (blockMachine program control alphabet blocks)).run _ _ _ =
    (unarySwapMachine (blockMachine program control alphabet blocks)).observe _ _ _
  rw [← unarySwap_decisionData n, unarySwap_run, unarySwap_observe]
  congr 1
  simpa using execution

omit [Fintype Γ] in
theorem unaryBlock_deterministic (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks Unit Γ) :
    (unaryBlockMachine program control alphabet blocks).Deterministic :=
  unarySwap_deterministic _ (blockMachine_deterministic program control alphabet blocks)

/-- Fixed prefix and per-input-cell blocks implement an affine unary expansion. -/
def affineUnaryBlocks (offset scale : ℕ) : InputBlocks Unit Bool where
  leading := List.replicate offset true
  trailing := []
  block := fun _ => List.replicate scale true

@[simp] theorem affineUnaryBlocks_word (offset scale n : ℕ) :
    (affineUnaryBlocks offset scale).word (List.replicate n ()) =
      List.replicate (offset + scale * n) true := by
  simp [InputBlocks.word, affineUnaryBlocks, List.flatMap_replicate, Nat.mul_comm]

/-- The collision reduction's index is materialised by a real machine starting
with a blank work tape. Loading and rewinding cost exactly `10 * n + 17` steps. -/
theorem collisionIndex_bootstrap (program : TM0.Machine Bool Q) (control : Q ≃ Fin states)
    (alphabet : Bool ≃ Fin symbols) (n : ℕ) (bits : BitString) :
    ∃ ready, PostRelated (unaryBlockSimulator program control alphabet (affineUnaryBlocks 6 4))
        (TM0.init (List.replicate (4 * (n + 1) + 2) true)) ready ∧
      (unaryBlockMachine program control alphabet (affineUnaryBlocks 6 4)).run (generatorData n) bits
          (10 * n + 17) =
        (unaryBlockMachine program control alphabet (affineUnaryBlocks 6 4)).observe
          (generatorData n) bits ready := by
  have size : 6 + 4 * n = 4 * (n + 1) + 2 := by omega
  have clock : 2 * (4 * (n + 1) + 2) + 2 * n + 5 = 10 * n + 17 := by omega
  simpa only [affineUnaryBlocks_word, size, List.length_replicate, clock] using
    unaryBlock_bootstrap program control alphabet (affineUnaryBlocks 6 4) n bits

/-- A cofinal polynomial bound on the actual index-loading transitions. -/
def collisionIndexLoadingBound : PolynomialBound := ⟨17, 1, by decide⟩

theorem collisionIndexLoadingBound_le (n : ℕ) :
    10 * n + 17 ≤ collisionIndexLoadingBound n := by
  simp [collisionIndexLoadingBound, PolynomialBound.eval]
  omega

end

end ComplexityOfGenerators.Simulation
