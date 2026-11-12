import ComplexityOfGenerators.Simulation.TransducerBank.Space
import ComplexityOfGenerators.Generators

/-!
# The finite multitape model for general resource bounds

The paper explicitly permits a fixed number of work tapes in its general
resource characterisations. `MultitapeMachine` bundles the existing executable
`tape-bank` model, rather than charging the quadratic single-tape compiler as
one transition. A bank instruction inspects one selected work cell; the number
of tapes is fixed by the finite program. Random reads and emitted symbols each
cost a transition, as in the native model.

These definitions do not replace the native `Machine` or its language classes.
In particular, an arbitrary-time theorem about this model must not be inferred
from the quadratic native compiler. `SpaceBound` is the existing head-radius
bound; on a fixed finite bank this is equivalent, within constant factors, to
counting visited work cells on all tapes.
-/

namespace ComplexityOfGenerators

open Simulation.TransducerBank

/-- A genuine finite transition table with a fixed finite bank of work tapes. -/
structure MultitapeMachine (I A O : Type) where
  inputFinite : Finite I
  auxiliaryFinite : Finite A
  outputFinite : Finite O
  Control : Type
  Work : Type
  controlFinite : Fintype Control
  workFinite : Fintype Work
  tapes : ℕ
  program : TapeBank I A O Control Work tapes

attribute [instance] MultitapeMachine.controlFinite MultitapeMachine.workFinite

namespace MultitapeMachine

variable {I A O : Type} (M : MultitapeMachine I A O)

abbrev Configuration := BankConfiguration O M.Control M.Work M.tapes

abbrev initialConfiguration : M.Configuration := M.program.initialConfiguration

abbrev Executes (data : InputData I A) (bits : BitString)
    (c : M.Configuration) (ticks : ℕ) (result : Outcome O) : Prop :=
  M.program.Executes data bits c ticks result

/-- Finite-bit executions always terminate, including short choice tapes. -/
def Terminates (data : InputData I A) : Prop :=
  ∀ bits, ∃ ticks result, M.Executes data bits M.initialConfiguration ticks result

def Produces (data : InputData I A) (bits : BitString) (word : Word O) : Prop :=
  ∃ ticks, M.Executes data bits M.initialConfiguration ticks (.accepted word)

def Accepts (data : InputData I A) (bits : BitString) : Prop :=
  ∃ word, M.Produces data bits word

def generatedLanguage (data : InputData I A) : Language O :=
  {word | ∃ bits, bits ≠ [] ∧ M.Produces data bits word}

def acceptedStreams (data : InputData I A) : Set BitStream :=
  {stream | ∃ bits, stream ∈ cylinder bits ∧ M.Accepts data bits}

/-- No explicit rejection: a failed finite trial ends by random exhaustion. -/
def HaltingTransducer (data : InputData I A) : Prop :=
  M.Terminates data ∧
    ∀ bits ticks, ¬ M.Executes data bits M.initialConfiguration ticks .rejected

def IsGenerator (data : InputData I A) : Prop :=
  M.HaltingTransducer data ∧
    (fairCoinMeasure (M.acceptedStreams data) = 1 ∨
      fairCoinMeasure (M.acceptedStreams data) = 0)

/-- Every branch terminates within the bound. The choice tape is not advice. -/
def TimeBound (data : InputData I A) (time : ℕ) : Prop :=
  ∀ bits, ∃ ticks result, ticks ≤ time ∧
    M.Executes data bits M.initialConfiguration ticks result

/-- Only accepted branches are bounded, exactly as in paper Definition 4.3. -/
def AcceptingTimeBound (data : InputData I A) (time : ℕ) : Prop :=
  ∀ bits ticks word,
    M.Executes data bits M.initialConfiguration ticks (.accepted word) → ticks ≤ time

abbrev SpaceBound (data : InputData I A) (space : ℕ) : Prop :=
  M.program.SpaceBound data space

abbrev Deterministic : Prop := M.program.Deterministic

/-- The existing actual finite compiler. Its time cost is quadratic, not linear. -/
noncomputable def toNative [Fintype I] [Fintype A] [Fintype O] : Machine I A O :=
  bankMachine M.program

theorem executes_toNative [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (bits : BitString) (ticks : ℕ) (result : Outcome O)
    (execution : M.Executes data bits M.initialConfiguration ticks result) :
    ∃ nativeTicks, nativeTicks ≤ 1 + (ticks + 1) * (2 * ticks + 4) ∧
      M.toNative.run data bits nativeTicks = .halted result :=
  bank_run M.program data bits ticks result execution

theorem timeBound_toNative [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (time : ℕ) (bounded : M.TimeBound data time) :
    M.toNative.TimeBound data (1 + (time + 1) * (2 * time + 4)) := by
  intro bits
  obtain ⟨ticks, result, small, execution⟩ := bounded bits
  obtain ⟨nativeTicks, cost, run⟩ := M.executes_toNative data bits ticks result execution
  have large : nativeTicks ≤ 1 + (time + 1) * (2 * time + 4) := by
    apply cost.trans
    have first : ticks + 1 ≤ time + 1 := Nat.add_le_add_right small 1
    have second : 2 * ticks + 4 ≤ 2 * time + 4 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 small) 4
    exact Nat.add_le_add_left (Nat.mul_le_mul first second) 1
  refine ⟨result, ?_⟩
  have := M.toNative.run_halted_add data bits nativeTicks result run
    (1 + (time + 1) * (2 * time + 4) - nativeTicks)
  simpa only [Nat.add_sub_of_le large] using this

/-- Forward compilation and finite-branch termination exclude spurious native
acceptance; no unproved reverse simulation is used. -/
theorem produces_toNative_iff [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (terminates : M.Terminates data)
    (bits : BitString) (word : Word O) :
    M.toNative.Produces data bits word ↔ M.Produces data bits word := by
  constructor
  · rintro ⟨nativeTicks, nativeRun⟩
    obtain ⟨ticks, result, execution⟩ := terminates bits
    obtain ⟨compiledTicks, _, compiledRun⟩ :=
      M.executes_toNative data bits ticks result execution
    have same := M.toNative.halted_outcome_unique data bits nativeTicks compiledTicks
      (.accepted word) result nativeRun compiledRun
    subst result
    exact ⟨ticks, execution⟩
  · rintro ⟨ticks, execution⟩
    obtain ⟨nativeTicks, _, compiledRun⟩ :=
      M.executes_toNative data bits ticks (.accepted word) execution
    exact ⟨nativeTicks, compiledRun⟩

theorem accepts_toNative_iff [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (terminates : M.Terminates data) (bits : BitString) :
    M.toNative.Accepts data bits ↔ M.Accepts data bits :=
  exists_congr (fun word => M.produces_toNative_iff data terminates bits word)

theorem generatedLanguage_toNative [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (terminates : M.Terminates data) :
    M.toNative.generatedLanguage data = M.generatedLanguage data := by
  ext word
  exact exists_congr fun bits => and_congr_right fun _ =>
    M.produces_toNative_iff data terminates bits word

theorem acceptedStreams_toNative [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (terminates : M.Terminates data) :
    M.toNative.acceptedStreams data = M.acceptedStreams data := by
  ext stream
  exact exists_congr fun bits => and_congr_right fun _ =>
    M.accepts_toNative_iff data terminates bits

theorem isGenerator_toNative [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (generator : M.IsGenerator data) :
    M.toNative.IsGenerator data := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro bits
    obtain ⟨ticks, result, execution⟩ := generator.1.1 bits
    obtain ⟨nativeTicks, _, compiledRun⟩ :=
      M.executes_toNative data bits ticks result execution
    exact ⟨nativeTicks, result, compiledRun⟩
  · intro bits nativeTicks nativeRun
    obtain ⟨ticks, result, execution⟩ := generator.1.1 bits
    obtain ⟨compiledTicks, _, compiledRun⟩ :=
      M.executes_toNative data bits ticks result execution
    have same := M.toNative.halted_outcome_unique data bits nativeTicks compiledTicks
      .rejected result nativeRun compiledRun
    subst result
    exact generator.1.2 bits ticks execution
  · rw [M.acceptedStreams_toNative data generator.1.1]
    exact generator.2

end MultitapeMachine
end ComplexityOfGenerators
