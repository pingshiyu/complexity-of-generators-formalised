import ComplexityOfGenerators.Simulation.PostMachine
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Loading a block encoding from the original input alphabet

This is a finite transition-table construction. Each source input symbol
selects a fixed finite block; no unbounded encoding function executes inside
one machine transition. Prefix and trailing blocks allow stack delimiters and
initial accumulator values to be supplied by the loader.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

structure InputBlocks (I Γ : Type) where
  leading : List Γ
  trailing : List Γ
  block : I → List Γ

def InputBlocks.word {I Γ : Type} (blocks : InputBlocks I Γ) (input : List I) : List Γ :=
  blocks.leading ++ input.flatMap blocks.block ++ blocks.trailing

inductive LoaderState (I : Type) (leading trailing : ℕ) (width : I → ℕ) (states : ℕ)
  | start
  | mark
  | leading : Fin leading → LoaderState I leading trailing width states
  | input
  | block : (letter : I) → Fin (width letter) → LoaderState I leading trailing width states
  | advance
  | trailing : Fin trailing → LoaderState I leading trailing width states
  | rewind
  | run : Fin states → LoaderState I leading trailing width states
  deriving Fintype

variable {I Γ Q : Type} [Fintype I] [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

abbrev BlockControl (blocks : InputBlocks I Γ) (states : ℕ) :=
  LoaderState I blocks.leading.length blocks.trailing.length (fun letter => (blocks.block letter).length) states

noncomputable def blockControl (blocks : InputBlocks I Γ) :
    BlockControl blocks states ≃ Fin (Fintype.card (BlockControl blocks states)) := Fintype.equivFin _

def InputBlocks.firstPrefix (blocks : InputBlocks I Γ) : BlockControl blocks states :=
  if h : 0 < blocks.leading.length then .leading ⟨0, h⟩ else .input

def InputBlocks.firstSuffix (blocks : InputBlocks I Γ) : BlockControl blocks states :=
  if h : 0 < blocks.trailing.length then .trailing ⟨0, h⟩ else .rewind

noncomputable def blockTransition (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ)
    (phase : BlockControl blocks states) (input : Option I) (work : Option (Fin (symbols + 1))) :
    Instruction Unit (Fintype.card (BlockControl blocks states)) (symbols + 1) :=
  let state := blockControl blocks
  match phase with
  | .start => .step (state .mark) none .left .stay .stay .stay none
  | .mark => .step (state blocks.firstPrefix) (some (Fin.last symbols)) .right .stay .stay .stay none
  | .leading i =>
      .step (state (if h : i.val + 1 < blocks.leading.length then .leading ⟨i.val + 1, h⟩ else .input))
        (some (bootEncode alphabet blocks.leading[i])) .right .stay .stay .stay none
  | .input => match input with
      | some letter => if h : 0 < (blocks.block letter).length then
          .step (state (.block letter ⟨0, h⟩)) none .stay .stay .stay .stay none
        else .step (state .advance) none .stay .stay .stay .stay none
      | none => .step (state blocks.firstSuffix) none .stay .stay .stay .stay none
  | .block letter i =>
      if h : i.val + 1 < (blocks.block letter).length then
        .step (state (.block letter ⟨i.val + 1, h⟩))
          (some (bootEncode alphabet (blocks.block letter)[i])) .right .stay .stay .stay none
      else .step (state .advance) (some (bootEncode alphabet (blocks.block letter)[i]))
        .right .stay .stay .stay none
  | .advance => .step (state .input) none .stay .right .stay .stay none
  | .trailing i =>
      .step (state (if h : i.val + 1 < blocks.trailing.length then .trailing ⟨i.val + 1, h⟩ else .rewind))
        (some (bootEncode alphabet blocks.trailing[i])) .right .stay .stay .stay none
  | .rewind => if work = some (Fin.last symbols) then
        .step (state (.run (control default))) none .right .stay .stay .stay none
      else .step (state .rewind) none .left .stay .stay .stay none
  | .run q => postInstruction (fun q => state (.run (control q))) (bootEncode alphabet)
      (program (control.symm q) (bootDecode alphabet work))

noncomputable def blockMachine (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) : Machine I Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (BlockControl blocks states)
  symbols := symbols + 1
  initial := blockControl blocks .start
  transition := fun q input _ _ work => blockTransition program control alphabet blocks
    ((blockControl blocks).symm q) input work

noncomputable def blockSimulator (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) : PostSimulator program I where
  machine := blockMachine program control alphabet blocks
  control := fun q => blockControl blocks (.run (control q))
  encode := bootEncode alphabet
  decode := bootDecode alphabet
  writeCorrect := bootDecode_encode alphabet
  transitionCorrect := by
    intro q input auxiliary index work
    simp [blockMachine, blockTransition]

omit [Fintype Γ] in
theorem blockMachine_deterministic (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) :
    (blockMachine program control alphabet blocks).Deterministic := by
  intro q input auxiliary index work
  simp only [blockMachine]
  unfold blockTransition
  cases (blockControl blocks).symm q <;> simp only
  all_goals try { split_ifs <;> trivial }
  · cases input <;> simp only
    all_goals try { split_ifs <;> trivial }
  · cases program (control.symm _) (bootDecode alphabet work) with
    | none => trivial
    | some action => rcases action with ⟨q, action⟩; cases action <;> trivial

end ComplexityOfGenerators.Simulation
