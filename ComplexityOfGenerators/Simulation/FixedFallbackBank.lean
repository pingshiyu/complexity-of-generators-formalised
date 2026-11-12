import ComplexityOfGenerators.Simulation.AuxiliaryDecision
import ComplexityOfGenerators.Simulation.CompositionHandoff
import ComplexityOfGenerators.Simulation.TransducerBank.Embedding

/-! A bounded-word sampler followed by a decision branch.  On rejection a
fixed word is emitted.  A finite-control index test disables the whole machine
below the length of that word. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive FixedFallbackPhase (samplerStates states limit : ℕ) (α : Type := Bool)
  | check (remaining : Fin (limit + 1))
  | rewind (remaining : Fin (limit + 1))
  | source (q : CompositionPhase samplerStates states α)
  | reset | emit
  | constant (position : Fin (limit + 1))
  | drain
  deriving Fintype

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (fallback : List α)

abbrev FixedFallbackState := FixedFallbackPhase S.states M.states fallback.length α
abbrev FixedFallbackSymbol := CompositionCell S.symbols M.symbols α
abbrev FixedFallbackConfiguration :=
  TransducerBank.BankConfiguration α (FixedFallbackState S M fallback) (FixedFallbackSymbol S M) 4

def fixedFallbackSelect : FixedFallbackState S M fallback → Fin 4
  | .source q => compositionSelect S (auxiliaryDecision M) q
  | .reset | .emit => 2
  | _ => 0

def fixedFallbackSourceInstruction (cell : FixedFallbackSymbol S M) :
    TransducerBank.BankInstruction (CompositionState S (auxiliaryDecision M)) (FixedFallbackSymbol S M) α →
      TransducerBank.BankInstruction (FixedFallbackState S M fallback) (FixedFallbackSymbol S M) α
  | .accept => .step .reset cell .stay .stay .stay .stay none
  | .reject => .step (.constant 0) cell .stay .stay .stay .stay none
  | .readRandom no yes => .readRandom (.source no) (.source yes)
  | .step next write work input auxiliary index emit =>
      .step (.source next) write work input auxiliary index emit

def fixedFallbackTransition (q : FixedFallbackState S M fallback) (index : Option Unit)
    (origin : Bool) (cell : FixedFallbackSymbol S M) :
    TransducerBank.BankInstruction (FixedFallbackState S M fallback) (FixedFallbackSymbol S M) α :=
  match q with
  | .check remaining =>
      if remaining.val = 0 then
        .step (.rewind ⟨fallback.length, Nat.lt_succ_self _⟩) cell .stay .stay .stay .stay none
      else if index.isSome then
        .step (.check ⟨remaining.val - 1, by omega⟩) cell .stay .stay .stay .right none
      else .step .drain cell .stay .stay .stay .stay none
  | .rewind remaining =>
      if remaining.val = 0 then .step (.source .load) cell .stay .stay .stay .stay none
      else .step (.rewind ⟨remaining.val - 1, by omega⟩) cell .stay .stay .stay .left none
  | .source q => fixedFallbackSourceInstruction S M fallback cell
      (compositionTransition S (auxiliaryDecision M) q index origin cell)
  | .reset => .step (if origin then .emit else .reset) cell
      (if origin then .stay else .left) .stay .stay .stay none
  | .emit => match cell.certificate with
      | none => .accept
      | some letter => .step .emit cell .right .stay .stay .stay (some letter)
  | .constant position =>
      if inside : position.val < fallback.length then
        .step (.constant ⟨position.val + 1, by omega⟩) cell .stay .stay .stay .stay
          (some fallback[position.val])
      else .accept
  | .drain => .readRandom .drain .drain

def fixedFallbackBank : TransducerBank.TapeBank Unit Bool α
    (FixedFallbackState S M fallback) (FixedFallbackSymbol S M) 4 where
  initial := .check ⟨fallback.length, Nat.lt_succ_self _⟩
  blank := {}
  select := fixedFallbackSelect S M fallback
  transition := fun q _ _ index origin cell => fixedFallbackTransition S M fallback q index origin cell

theorem fixedFallback_source_path {n : ℕ} {bits : BitString}
    {c d : CompositionConfiguration S (auxiliaryDecision M)} {t : ℕ}
    (path : (samplerCompositionBank S (auxiliaryDecision M)).Steps (generatorData n) bits c t d) :
    (fixedFallbackBank S M fallback).Steps (generatorData n) bits
      (c.mapState FixedFallbackPhase.source) t (d.mapState FixedFallbackPhase.source) := by
  apply TransducerBank.TapeBank.Steps.mapState _ _ FixedFallbackPhase.source (fun _ => rfl) ?_ ?_ path
  · intro q i a x origin cell next write work input auxiliary index emit table
    change compositionTransition S (auxiliaryDecision M) q x origin cell = _ at table
    simp only [fixedFallbackBank, fixedFallbackTransition, table, fixedFallbackSourceInstruction]
  · intro q i a x origin cell no yes table
    change compositionTransition S (auxiliaryDecision M) q x origin cell = _ at table
    simp only [fixedFallbackBank, fixedFallbackTransition, table, fixedFallbackSourceInstruction]

end
end ComplexityOfGenerators.Simulation
