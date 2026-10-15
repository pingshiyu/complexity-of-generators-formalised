import ComplexityOfGenerators.Foundations.RunSimulation
import ComplexityOfGenerators.Foundations.BinaryCollisions
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.EquivFin

/-!
# A native binary-output decoder with no time overhead

Two canonical output bits represent one pair symbol. The adapter stores at most
one pending bit in finite control and emits a decoded symbol during the original
machine's second emitting transition. Every source transition costs exactly one
target transition. Malformed output is harmless for a general collision finder;
only correctness on canonical encoded collisions is needed by the reduction.
-/

namespace ComplexityOfGenerators.Simulation

/-- Total streaming decoder. The unused block `11` is assigned the separator;
a trailing unpaired bit is retained in finite control and emits nothing. -/
def decodeOutputBit (pending : Option Bool) (bit : Bool) : Option Bool × Option PairSymbol :=
  match pending with
  | none => (some bit, none)
  | some first => (none, some (if first then .separator else .bit bit))

def decodeOutputStep (state : Option Bool × List PairSymbol) (bit : Bool) :
    Option Bool × List PairSymbol :=
  let action := decodeOutputBit state.1 bit
  (action.1, state.2 ++ action.2.toList)

def decodeOutput (bits : BitString) : Option Bool × List PairSymbol :=
  bits.foldl decodeOutputStep (none, [])

theorem decodeOutput_snoc (bits : BitString) (bit : Bool) :
    decodeOutput (bits ++ [bit]) = decodeOutputStep (decodeOutput bits) bit := by
  simp [decodeOutput, List.foldl_append]

theorem decodeOutput_fold_encoded (word : List PairSymbol) (out : List PairSymbol) :
    (binaryPairWord word).foldl decodeOutputStep (none, out) = (none, out ++ word) := by
  induction word generalizing out with
  | nil => simp [binaryPairWord]
  | cons symbol tail ih =>
      have step : (pairSymbolBits symbol).foldl decodeOutputStep (none, out) =
          (none, out ++ [symbol]) := by
        cases symbol <;> simp [pairSymbolBits, decodeOutputStep, decodeOutputBit]
      change (pairSymbolBits symbol ++ binaryPairWord tail).foldl decodeOutputStep (none, out) = _
      rw [List.foldl_append, step, ih]
      simp [List.append_assoc]

@[simp] theorem decodeOutput_encoded (word : List PairSymbol) :
    decodeOutput (binaryPairWord word) = (none, word) := by
  simpa [decodeOutput] using decodeOutput_fold_encoded word []

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A : Type} (M : Machine I A Bool)

def decodeOutputControl : (Fin M.states × Option Bool) ≃ Fin (Fintype.card (Fin M.states × Option Bool)) :=
  Fintype.equivFin _

def decodeOutputInstruction (pending : Option Bool) : Instruction Bool M.states M.symbols →
    Instruction PairSymbol (Fintype.card (Fin M.states × Option Bool)) M.symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (decodeOutputControl M (no, pending)) (decodeOutputControl M (yes, pending))
  | .step next write work input auxiliary index none =>
      .step (decodeOutputControl M (next, pending)) write work input auxiliary index none
  | .step next write work input auxiliary index (some bit) =>
      let action := decodeOutputBit pending bit
      .step (decodeOutputControl M (next, action.1)) write work input auxiliary index action.2

def binaryOutputDecoder : Machine I A PairSymbol where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  states := Fintype.card (Fin M.states × Option Bool)
  symbols := M.symbols
  initial := decodeOutputControl M (M.initial, none)
  transition := fun state input auxiliary index work =>
    let source := (decodeOutputControl M).symm state
    decodeOutputInstruction M source.2 (M.transition source.1 input auxiliary index work)

def decodeOutputConfiguration (c : Configuration M) : Configuration (binaryOutputDecoder M) where
  state := decodeOutputControl M (c.state, (decodeOutput c.output).1)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := (decodeOutput c.output).2

def decodeOutputOutcome : Outcome Bool → Outcome PairSymbol
  | .accepted word => .accepted (decodeOutput word).2
  | .rejected => .rejected
  | .exhausted => .exhausted

def decodeOutputResult : RunState M → RunState (binaryOutputDecoder M)
  | .running c => .running (decodeOutputConfiguration M c)
  | .halted result => .halted (decodeOutputOutcome result)

theorem binaryOutputDecoder_observe (data : InputData I A) (bits : BitString) (c : Configuration M) :
    (binaryOutputDecoder M).observe data bits (decodeOutputConfiguration M c) =
      decodeOutputResult M (M.observe data bits c) := by
  simp only [Machine.observe, binaryOutputDecoder, decodeOutputConfiguration, Equiv.symm_apply_apply]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes => split_ifs <;> rfl
  | step next write work input auxiliary index emit => cases emit <;> rfl

theorem binaryOutputDecoder_next (data : InputData I A) (bits : BitString) (c : Configuration M) :
    (binaryOutputDecoder M).next data bits (decodeOutputConfiguration M c) =
      decodeOutputResult M (M.next data bits c) := by
  simp only [Machine.next, binaryOutputDecoder, decodeOutputConfiguration, Equiv.symm_apply_apply]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes =>
      simp only [decodeOutputInstruction]
      cases bits[c.randomHead]? with
      | none => rfl
      | some bit => cases bit <;> rfl
  | step next write work input auxiliary index emit =>
      cases emit with
      | none => cases write <;> rfl
      | some bit =>
          simp only [decodeOutputInstruction, decodeOutputResult, decodeOutputConfiguration,
            decodeOutput_snoc, decodeOutputStep]
          cases pending : (decodeOutput c.output).1 <;>
            simp only [decodeOutputBit, Option.toList_none, Option.toList_some, List.append_nil]
          all_goals cases write <;> rfl

/-- Exact clock correspondence, including explicit rejection and exhaustion. -/
theorem binaryOutputDecoder_run (data : InputData I A) (bits : BitString) (t : ℕ) :
    (binaryOutputDecoder M).run data bits t = decodeOutputResult M (M.run data bits t) :=
  Machine.run_map (fun _ => rfl) (fun _ => rfl)
    (binaryOutputDecoder_observe M data bits) (binaryOutputDecoder_next M data bits) rfl t

theorem binaryOutputDecoder_timeBound (data : InputData I A) (t : ℕ)
    (bound : M.TimeBound data t) : (binaryOutputDecoder M).TimeBound data t := by
  intro bits
  obtain ⟨result, halted⟩ := bound bits
  exact ⟨decodeOutputOutcome result, by rw [binaryOutputDecoder_run, halted]; rfl⟩

/-- On canonical words the concrete native decoder recovers the exact source
alphabet, preserving both the seed and the transition budget. -/
theorem binaryOutputDecoder_produces (data : InputData I A) (bits : BitString) (word : List PairSymbol)
    (produced : M.Produces data bits (binaryPairWord word)) :
    (binaryOutputDecoder M).Produces data bits word := by
  obtain ⟨t, execution⟩ := produced
  refine ⟨t, ?_⟩
  rw [binaryOutputDecoder_run, execution]
  simp [decodeOutputResult, decodeOutputOutcome]

end

end ComplexityOfGenerators.Simulation
