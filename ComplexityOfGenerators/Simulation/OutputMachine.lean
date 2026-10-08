import ComplexityOfGenerators.Simulation.OutputEncoding

/-!
# A finite-control word-output routine

The output alphabet is finite. Consequently all prefixes of all its binary
letter encodings form a finite dictionary. Scanning a bit selects the next
dictionary entry; a delimiter emits one letter. The transition table performs
only a single native movement or emission at each step. There is no unbounded
decoder hidden inside a transition.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] [Encodable α]

noncomputable def outputPrefixes (α : Type) [Fintype α] [Encodable α] :
    Finset (List PartrecToTM2.Γ') := by
  classical
  exact insert [] (Finset.univ.biUnion fun letter : α => (outputBlock letter).inits.toFinset)

abbrev OutputPrefix (α : Type) [Fintype α] [Encodable α] := ↥(outputPrefixes α)

theorem empty_mem_outputPrefixes : ([] : List PartrecToTM2.Γ') ∈ outputPrefixes α := by
  classical
  simp [outputPrefixes]

theorem prefix_mem_outputPrefixes {letter : α} {p : List PartrecToTM2.Γ'}
    (initial : p <+: outputBlock letter) : p ∈ outputPrefixes α := by
  classical
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨letter, Finset.mem_univ _, List.mem_toFinset.mpr
    ((List.mem_inits _ _).mpr initial)⟩

def emptyOutputPrefix : OutputPrefix α := ⟨[], empty_mem_outputPrefixes⟩

noncomputable def extendOutputPrefix (p : OutputPrefix α) (symbol : PartrecToTM2.Γ') :
    Option (OutputPrefix α) := by
  classical
  exact if h : p.val ++ [symbol] ∈ outputPrefixes α then some ⟨p.val ++ [symbol], h⟩ else none

theorem extendOutputPrefix_correct (p : OutputPrefix α) (symbol : PartrecToTM2.Γ')
    (available : p.val ++ [symbol] ∈ outputPrefixes α) :
    extendOutputPrefix p symbol = some ⟨p.val ++ [symbol], available⟩ := by
  classical
  simp [extendOutputPrefix, available]

noncomputable def decodeOutputPrefix (p : List PartrecToTM2.Γ') : Option α := by
  classical
  exact if h : ∃ letter : α, outputBlock letter = p then some h.choose else none

theorem decodeOutputPrefix_correct (letter : α) :
    decodeOutputPrefix (outputBlock letter) = some letter := by
  classical
  have existsLetter : ∃ a : α, outputBlock a = outputBlock letter := ⟨letter, rfl⟩
  simp only [decodeOutputPrefix, dite_eq_left existsLetter]
  exact congrArg some (outputBlock_injective existsLetter.choose_spec)

theorem decodeOutputPrefix_sound {p : List PartrecToTM2.Γ'} {letter : α}
    (decoded : decodeOutputPrefix p = some letter) : outputBlock letter = p := by
  classical
  unfold decodeOutputPrefix at decoded
  split_ifs at decoded with h
  · cases Option.some.inj decoded
    exact h.choose_spec

inductive OutputControl (α : Type) [Fintype α] [Encodable α]
  | start
  | scan : OutputPrefix α → OutputControl α
  | finish
  deriving Fintype

noncomputable def outputControl : OutputControl α ≃ Fin (Fintype.card (OutputControl α)) :=
  Fintype.equivFin _

noncomputable def outputInstruction {symbols : ℕ}
    (phase : OutputControl α) (symbol : Option PartrecToTM2.Γ') :
    Instruction α (Fintype.card (OutputControl α)) symbols :=
  match phase with
  | .start => match symbol with
    | none => .accept
    | some .cons => .step (outputControl (.scan emptyOutputPrefix)) none .right .stay .stay .stay none
    | _ => .reject
  | .finish => .accept
  | .scan p => match symbol with
    | some .bit0 => match extendOutputPrefix p .bit0 with
      | some next => .step (outputControl (.scan next)) none .right .stay .stay .stay none
      | none => .reject
    | some .bit1 => match extendOutputPrefix p .bit1 with
      | some next => .step (outputControl (.scan next)) none .right .stay .stay .stay none
      | none => .reject
    | some .cons => match decodeOutputPrefix p.val with
      | some letter => .step (outputControl (.scan emptyOutputPrefix)) none .right .stay .stay .stay (some letter)
      | none => .reject
    | none => match decodeOutputPrefix p.val with
      | some letter => .step (outputControl .finish) none .stay .stay .stay .stay (some letter)
      | none => .reject
    | _ => .reject

/-- The tape projection reads just the main stack component of a work symbol.
It is supplied explicitly so the routine can share the compiler's work alphabet. -/
noncomputable def outputMachine (symbols : ℕ)
    (read : Option (Fin symbols) → Option PartrecToTM2.Γ') : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (OutputControl α)
  symbols := symbols
  initial := outputControl .start
  transition := fun q _ _ _ work => outputInstruction (outputControl.symm q) (read work)

theorem outputMachine_deterministic (symbols : ℕ)
    (read : Option (Fin symbols) → Option PartrecToTM2.Γ') :
    (outputMachine (α := α) symbols read).Deterministic := by
  intro q input auxiliary index work
  simp only [outputMachine]
  unfold outputInstruction
  cases outputControl.symm q with
  | start => cases read work with
    | none => trivial
    | some symbol => cases symbol <;> trivial
  | finish => trivial
  | scan p =>
      cases read work with
      | none => simp only; cases decodeOutputPrefix (α := α) p.val <;> trivial
      | some symbol =>
          cases symbol <;> simp only
          · cases decodeOutputPrefix (α := α) p.val <;> trivial
          · cases extendOutputPrefix p .bit0 <;> trivial
          · cases extendOutputPrefix p .bit1 <;> trivial

end

end ComplexityOfGenerators.Simulation
