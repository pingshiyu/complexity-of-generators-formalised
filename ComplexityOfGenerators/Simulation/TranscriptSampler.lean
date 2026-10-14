import ComplexityOfGenerators.Foundations.ExecutionTranscripts
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# A finite machine recording its source's computation

The sampler emits an initial padding bit, then one bit per source transition:
`false` for an ordinary instruction and the actual choice for a random read.
Source output is discarded. Each source transition uses two primitive sampler
steps, and the source's random cursor is preserved exactly. The extra phase
makes the overhead uniform without adding a clock or a semantic oracle.
-/

namespace ComplexityOfGenerators.Simulation

inductive SamplerPhase (states : ℕ)
  | boot
  | execute (state : Fin states)
  | pad (state : Fin states)
  | emit (state : Fin states) (bit : Bool)
  deriving Fintype

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

def samplerControl : SamplerPhase M.states ≃ Fin (Fintype.card (SamplerPhase M.states)) :=
  Fintype.equivFin _

def samplerInstruction : Instruction O M.states M.symbols →
    Instruction Bool (Fintype.card (SamplerPhase M.states)) M.symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes =>
      .readRandom (samplerControl M (.emit no false)) (samplerControl M (.emit yes true))
  | .step next write work input auxiliary index _ =>
      .step (samplerControl M (.pad next)) write work input auxiliary index (some false)

def transcriptSampler : Machine I A Bool where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  states := Fintype.card (SamplerPhase M.states)
  symbols := M.symbols
  initial := samplerControl M .boot
  transition := fun q input auxiliary index work => match (samplerControl M).symm q with
    | .boot => .step (samplerControl M (.execute M.initial)) none .stay .stay .stay .stay (some false)
    | .execute state => samplerInstruction M (M.transition state input auxiliary index work)
    | .pad state => .step (samplerControl M (.execute state)) none .stay .stay .stay .stay none
    | .emit state bit => .step (samplerControl M (.execute state)) none .stay .stay .stay .stay (some bit)

def samplerConfiguration (c : Configuration M) (log : BitString)
    (phase : SamplerPhase M.states := .execute c.state) : Configuration (transcriptSampler M) where
  state := samplerControl M phase
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := log

/-- Stationary helper steps preserve all simulated tape data. The hypotheses
are the ordinary reachable-head invariants, including the visited work cell. -/
theorem sampler_helper (data : InputData I A) (bits : BitString) (c : Configuration M)
    (log : BitString) (phase : SamplerPhase M.states) (emit : Option Bool)
    (inputBound : c.inputHead ≤ data.input.length) (auxiliaryBound : c.auxiliaryHead ≤ data.auxiliary.length)
    (indexBound : c.indexHead ≤ data.index) (head : c.workHead ∈ c.visited)
    (action : (transcriptSampler M).transition (samplerControl M phase)
      data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
      .step (samplerControl M (.execute c.state)) none .stay .stay .stay .stay emit) :
    let start := samplerConfiguration M c log phase
    let finish := samplerConfiguration M c (log ++ emit.toList)
    (transcriptSampler M).observe data bits start = .running start ∧
      (transcriptSampler M).next data bits start = .running finish := by
  dsimp only
  refine ⟨(transcriptSampler M).observe_step data bits _ _ _ _ _ _ _ _ action, ?_⟩
  rw [(transcriptSampler M).next_step data bits _ _ _ _ _ _ _ _ action]
  cases emit <;>
    simp [Machine.stepConfiguration, samplerConfiguration, Move.onInput, Move.onInt,
      Nat.min_eq_left inputBound, Nat.min_eq_left auxiliaryBound, Nat.min_eq_left indexBound,
      Finset.insert_eq_of_mem head]

theorem transcriptSampler_boot (data : InputData I A) (bits : BitString) :
    (transcriptSampler M).observe data bits (transcriptSampler M).initialConfiguration =
        .running (transcriptSampler M).initialConfiguration ∧
      (transcriptSampler M).next data bits (transcriptSampler M).initialConfiguration =
        .running (samplerConfiguration M M.initialConfiguration [false]) := by
  simp [Machine.observe, Machine.next, Machine.initialConfiguration, transcriptSampler,
    samplerConfiguration, Move.onInput, Move.onInt]

end
end ComplexityOfGenerators.Simulation
