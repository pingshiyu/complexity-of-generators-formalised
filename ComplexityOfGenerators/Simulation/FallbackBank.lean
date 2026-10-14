import ComplexityOfGenerators.Simulation.WordSampler
import ComplexityOfGenerators.Simulation.AuxiliaryDecision
import ComplexityOfGenerators.Simulation.CompositionHandoff
import ComplexityOfGenerators.Simulation.TransducerBank.Embedding

/-!
# The fallback generator's finite program

Sample a word, run an NP decision branch on it, and then emit either that word
or the constant fallback word of the same length. Empty slices are selected by
one hardwired Boolean, so an absent empty word causes random-tape exhaustion.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive FallbackPhase (states : ℕ)
  | boot | source (q : CompositionPhase 3 states)
  | reset (accepted : Bool) | emit (accepted : Bool) | drain
  deriving Fintype

variable (M : Machine Bool Bool Unit) (bit allowEmpty : Bool)

abbrev FallbackState := FallbackPhase M.states
abbrev FallbackSymbol := CompositionCell 0 M.symbols
abbrev FallbackConfiguration := TransducerBank.BankConfiguration Bool (FallbackState M) (FallbackSymbol M) 4

def fallbackSelect : FallbackState M → Fin 4
  | .source q => compositionSelect wordSampler (auxiliaryDecision M) q
  | .reset _ | .emit _ => 2
  | _ => 0

def fallbackSourceInstruction (cell : FallbackSymbol M) :
    TransducerBank.BankInstruction (CompositionState wordSampler (auxiliaryDecision M)) (FallbackSymbol M) Bool →
      TransducerBank.BankInstruction (FallbackState M) (FallbackSymbol M) Bool
  | .accept => .step (.reset true) cell .stay .stay .stay .stay none
  | .reject => .step (.reset false) cell .stay .stay .stay .stay none
  | .readRandom no yes => .readRandom (.source no) (.source yes)
  | .step next write work input auxiliary index emit =>
      .step (.source next) write work input auxiliary index emit

def fallbackTransition (q : FallbackState M) (index : Option Unit) (origin : Bool) (cell : FallbackSymbol M) :
    TransducerBank.BankInstruction (FallbackState M) (FallbackSymbol M) Bool :=
  match q with
  | .boot => .step (if index.isSome || allowEmpty then .source .load else .drain) cell .stay .stay .stay .stay none
  | .source q => fallbackSourceInstruction M cell (compositionTransition wordSampler (auxiliaryDecision M) q index origin cell)
  | .reset accepted => .step (if origin then .emit accepted else .reset accepted) cell
      (if origin then .stay else .left) .stay .stay .stay none
  | .emit accepted => match cell.certificate with
      | none => .accept
      | some letter => .step (.emit accepted) cell .right .stay .stay .stay (some (if accepted then letter else bit))
  | .drain => .readRandom .drain .drain

def fallbackBank : TransducerBank.TapeBank Unit Bool Bool (FallbackState M) (FallbackSymbol M) 4 where
  initial := .boot
  blank := {}
  select := fallbackSelect M
  transition := fun q _ _ index origin cell => fallbackTransition M bit allowEmpty q index origin cell

theorem fallback_source_path {n : ℕ} {bits : BitString}
    {c d : CompositionConfiguration wordSampler (auxiliaryDecision M)} {t : ℕ}
    (path : (samplerCompositionBank wordSampler (auxiliaryDecision M)).Steps (generatorData n) bits c t d) :
    (fallbackBank M bit allowEmpty).Steps (generatorData n) bits (c.mapState FallbackPhase.source) t (d.mapState FallbackPhase.source) := by
  apply TransducerBank.TapeBank.Steps.mapState _ _ FallbackPhase.source (fun _ => rfl) ?_ ?_ path
  · intro q i a x origin cell next write work input auxiliary index emit table
    change compositionTransition wordSampler (auxiliaryDecision M) q x origin cell = _ at table
    simp only [fallbackBank, fallbackTransition, table, fallbackSourceInstruction]
  · intro q i a x origin cell no yes table
    change compositionTransition wordSampler (auxiliaryDecision M) q x origin cell = _ at table
    simp only [fallbackBank, fallbackTransition, table, fallbackSourceInstruction]

theorem fallback_boot (n : ℕ) (bits : BitString) (live : n ≠ 0 ∨ allowEmpty = true) :
    (fallbackBank M bit allowEmpty).Steps (generatorData n) bits (fallbackBank M bit allowEmpty).initialConfiguration 1
      ((samplerCompositionBank wordSampler (auxiliaryDecision M)).initialConfiguration.mapState FallbackPhase.source) := by
  have positive : (0 < n) ∨ allowEmpty = true := live.imp (fun h => Nat.pos_of_ne_zero h) id
  have table : (fallbackBank M bit allowEmpty).instruction (generatorData n) (fallbackBank M bit allowEmpty).initialConfiguration =
      .step (.source .load) {} .stay .stay .stay .stay none := by
    rcases positive with h | h <;>
      simp [TransducerBank.TapeBank.instruction, TransducerBank.TapeBank.initialConfiguration,
        fallbackBank, fallbackTransition, fallbackSelect, generatorData, h]
  have step := TransducerBank.TapeBank.Steps.single (fallbackBank M bit allowEmpty) (generatorData n) bits _ _ _ _ _ _ _ _ table
  simpa [TransducerBank.TapeBank.advance, TransducerBank.TapeBank.initialConfiguration,
    TransducerBank.BankConfiguration.mapState, fallbackBank, fallbackSelect, samplerCompositionBank,
    Function.update_eq_self, Move.onInput, Move.onInt] using step

end
end ComplexityOfGenerators.Simulation
