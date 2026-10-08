import ComplexityOfGenerators.Foundations.AuxiliaryFuel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-!
# Native replay of step-by-step certificates

A certificate starts with one padding bit and then has one bit per source
transition. Ordinary transitions ignore their bit; random reads use it as the
choice. Thus every transition consumes certificate fuel, even if the source
loops without reading randomness. Acceptance preserves the source output;
rejection or insufficient fuel explicitly rejects. No computation is hidden
inside a transition, and no source time bound is assumed.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I O : Type} (M : Machine I Bool O)

def transcriptControl : Option (Fin M.states) ≃ Fin (Fintype.card (Option (Fin M.states))) :=
  Fintype.equivFin _

def transcriptInstruction (q : Option (Fin M.states)) (input : Option I)
    (auxiliary index : Option Bool) (work : Option (Fin M.symbols)) :
    Instruction O (Fintype.card (Option (Fin M.states))) M.symbols :=
  match q with
  | none => match auxiliary with
    | none => .reject
    | some _ => .step (transcriptControl M (some M.initial)) none .stay .stay .right .stay none
  | some state => match M.transition state input none index work with
    | .accept => .accept
    | .reject => .reject
    | .readRandom no yes => match auxiliary with
      | none => .reject
      | some bit => .step (transcriptControl M (some (if bit then yes else no)))
          none .stay .stay .right .stay none
    | .step next write work input _ index emit => match auxiliary with
      | none => .reject
      | some _ => .step (transcriptControl M (some next)) write work input .right index emit

def transcriptReplay : Machine I Bool O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  states := Fintype.card (Option (Fin M.states))
  symbols := M.symbols
  initial := transcriptControl M none
  transition := fun q input auxiliary index work =>
    transcriptInstruction M ((transcriptControl M).symm q) input auxiliary index work

theorem transcriptReplay_fuel : (transcriptReplay M).AuxiliaryFuel := by
  intro q input auxiliary index work
  dsimp only [transcriptReplay]
  cases (transcriptControl M).symm q with
  | none => cases auxiliary <;> simp [transcriptInstruction]
  | some state =>
      cases action : M.transition state input none index work <;> cases auxiliary <;>
        simp [transcriptInstruction, action]

theorem transcriptReplay_deterministic : (transcriptReplay M).Deterministic :=
  (transcriptReplay_fuel M).deterministic _

/-- Replay halts in at most the certificate length on every random tape,
including malformed certificates and nonterminating source machines. -/
theorem transcriptReplay_timeBound (data : InputData I Bool) :
    (transcriptReplay M).TimeBound data data.auxiliary.length :=
  (transcriptReplay_fuel M).timeBound _ data

/-- The leading padding bit is compulsory, so a zero-transition source run
still has a positive certificate. -/
theorem transcriptReplay_empty_certificate (input : List I) (index : ℕ) (bits : BitString) :
    (transcriptReplay M).run {input := input, index := index} bits 0 = .halted .rejected := by
  simp [Machine.run, Machine.observe, Machine.initialConfiguration, transcriptReplay,
    transcriptInstruction]

end

end ComplexityOfGenerators.Simulation
