import ComplexityOfGenerators.Simulation.ClockTick
import ComplexityOfGenerators.Simulation.VirtualIndexSimulation

/-! Relating source configurations to the clock's five data tracks and
suspending one genuine source instruction while the odometer is advanced. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

def ClockAction.instruction {O : Type} {states symbols : ℕ} :
    ClockAction O states symbols → Instruction O states symbols
  | .random no yes => .readRandom no yes
  | .step next write work input auxiliary index emit => .step next write work input auxiliary index emit

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

structure ClockSnapshot (length : ℕ) (digits : List ℕ)
    (source : Configuration M) (target : Configuration (polynomialClockCore M p)) : Prop where
  memory : PolynomialClockMemory M p length source.work (clockLocations digits) (some source.workHead) target.work
  random : target.randomHead = source.randomHead
  output : target.output = source.output
  input : target.inputHead = source.inputHead
  auxiliary : target.auxiliaryHead = source.auxiliaryHead
  index : target.indexHead = source.indexHead

structure ClockReady (length : ℕ) (digits : List ℕ) (remaining : Fin (p.coefficient + 1))
    (source : Configuration M) (negative : Bool) (target : Configuration (polynomialClockCore M p)) : Prop
    extends ClockSnapshot M p length digits source target where
  state : target.state = clockControl M p (.source source.state negative remaining)
  head : target.workHead = source.workHead
  side : if negative then source.workHead ≤ 0 else 0 ≤ source.workHead

theorem ClockSnapshot.readHeadBounds {data : InputData I A} {length : ℕ} {digits : List ℕ}
    {source : Configuration M} {target : Configuration (polynomialClockCore M p)}
    (h : ClockSnapshot M p length digits source target) (bounds : ReadHeadBounds M data source) :
    ReadHeadBounds (polynomialClockCore M p) data target := by
  constructor
  · rw [h.input]; exact bounds.input
  · rw [h.auxiliary]; exact bounds.auxiliary
  · rw [h.index]; exact bounds.index

theorem clock_suspend (data : InputData I A) (bits : BitString) (length : ℕ)
    (digits : List ℕ) (size : digits.length = p.degree) (bounded : ∀ d ∈ digits, d ≤ length)
    (remaining : Fin (p.coefficient + 1)) (positive : 0 < remaining.val)
    (source : Configuration M) (negative : Bool) (target : Configuration (polynomialClockCore M p))
    (related : ClockReady M p length digits remaining source negative target)
    (bounds : ReadHeadBounds M data source) (action : ClockAction O M.states M.symbols)
    (instruction : M.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some true else none) (source.work source.workHead) = action.instruction) :
    ∃ ticks ready, ticks ≤ 2 * source.workHead.natAbs + (p.degree + 1) * (2 * length + 5) + 3 ∧
      ready.state = clockControl M p (.execute action negative
        (clockNextBlock p remaining (clockDigitIncrement length digits).2)) ∧
      ready.workHead = source.workHead ∧
      ClockSnapshot M p length (clockDigitIncrement length digits).1 source ready ∧
      (polynomialClockCore M p).runFrom data bits target ticks =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  let entered := workStep N data target
    (clockControl M p (.toOrigin action negative remaining)) none .stay
  have enterRun : N.runFrom data bits target 1 = N.observe data bits entered := by
    apply workStep_run
    have readCell := related.memory source.workHead
    cases action <;>
      simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
        related.state, related.head, related.input, related.auxiliary, related.index,
        readCell, polynomialClockCell, instruction, ClockAction.instruction,
        show remaining.val ≠ 0 by omega]
  have targetBounds := related.toClockSnapshot.readHeadBounds M p bounds
  have enterFrame : WorkFrame N target entered := workStep_frame N data target _ none .stay targetBounds
  have position : source.workHead = signedPosition negative source.workHead.natAbs :=
    signedPosition_natAbs source.workHead negative related.side
  have enteredMemory : PolynomialClockMemory M p length source.work (clockLocations digits)
      (some (signedPosition negative source.workHead.natAbs)) entered.work := by
    rw [← position]; exact related.memory
  obtain ⟨ticks, ready, time, readyState, readyHead, readyMemory, readyFrame, readyRun⟩ :=
    clock_tick M p data bits length source.work digits size bounded action negative remaining source.workHead.natAbs
      entered (enterFrame.readHeadBounds N targetBounds) enteredMemory rfl (related.head.trans position)
  have frame := enterFrame.trans N readyFrame
  refine ⟨1 + ticks, ready, by omega, readyState, readyHead.trans position.symm,
    ⟨?_, frame.random.trans related.random, frame.output.trans related.output,
      frame.input.trans related.input, frame.auxiliary.trans related.auxiliary, frame.index.trans related.index⟩, ?_⟩
  · rw [← position] at readyMemory
    exact readyMemory
  · rw [N.runFrom_add data bits target entered 1 enterRun]
    exact readyRun

end

end ComplexityOfGenerators.Simulation
