import Mathlib.Data.Finset.Card
import Mathlib.Data.List.OfFn

/-!
# A finite-control machine model

The paper uses deterministic transducers driven by an explicit, read-once random
tape. This model has one two-way work tape, an append-only output tape, and
read-only tapes for ordinary input, auxiliary input, and the unary family index.
Unused input tapes are empty. Their heads are bounded by the end of their inputs;
they cannot serve as unbounded counters outside the space accounting.

One nonterminal instruction costs one time step. Halting and detecting a missing
random bit are observations of the current configuration, not extra transitions.
Only visited work-tape cells count as space.
The transition table is finite when the input/output alphabets are finite: both
control states and work symbols are `Fin` types. There is no arbitrary function
on configurations hidden in a transition.
-/

namespace ComplexityOfGenerators

abbrev BitString := List Bool
abbrev BitStream := ℕ → Bool
abbrev Word (α : Type) := List α
abbrev Language (α : Type) := Set (Word α)
abbrev LanguageClass (α : Type) := Set (Language α)

inductive Move where
  | left | stay | right
  deriving DecidableEq, Repr

def Move.onInt : Move → ℤ → ℤ
  | .left, i => i - 1
  | .stay, i => i
  | .right, i => i + 1

/-- Read-only input heads are clamped to the input and its right blank cell. -/
def Move.onInput : Move → ℕ → ℕ → ℕ
  | .left, _, i => i - 1
  | .stay, bound, i => min i bound
  | .right, bound, i => min (i + 1) bound

inductive Instruction (Output : Type) (states symbols : ℕ) where
  | accept
  | reject
  /-- Read and consume exactly one random bit; a missing bit causes exhaustion. -/
  | readRandom (onFalse onTrue : Fin states)
  /-- `none` means no write. Writing a blank symbol is not an instruction. -/
  | step (next : Fin states) (write : Option (Fin symbols))
      (workMove inputMove auxiliaryMove indexMove : Move) (emit : Option Output)

/-- A single finite transition table, shared across every family index. -/
structure Machine (Input Auxiliary Output : Type) where
  inputFinite : Finite Input
  auxiliaryFinite : Finite Auxiliary
  outputFinite : Finite Output
  states : ℕ
  symbols : ℕ
  initial : Fin states
  transition : Fin states → Option Input → Option Auxiliary → Option Bool →
    Option (Fin symbols) → Instruction Output states symbols

structure InputData (Input Auxiliary : Type) where
  input : List Input := []
  auxiliary : List Auxiliary := []
  /-- The read-only tape contains `index` copies of `true` (unary encoding). -/
  index : ℕ := 0

structure Configuration {I A O : Type} (M : Machine I A O) where
  state : Fin M.states
  inputHead : ℕ
  auxiliaryHead : ℕ
  indexHead : ℕ
  randomHead : ℕ
  workHead : ℤ
  work : ℤ → Option (Fin M.symbols)
  visited : Finset ℤ
  output : List O

/-- Explicit rejection and random-tape exhaustion are distinguished. -/
inductive Outcome (O : Type) where
  | accepted (output : List O)
  | rejected
  | exhausted
  deriving DecidableEq

inductive RunState {I A O : Type} (M : Machine I A O) where
  | running (configuration : Configuration M)
  | halted (outcome : Outcome O)

namespace Machine

variable {I A O : Type} (M : Machine I A O)

def initialConfiguration : Configuration M where
  state := M.initial
  inputHead := 0
  auxiliaryHead := 0
  indexHead := 0
  randomHead := 0
  workHead := 0
  work := fun _ => none
  visited := {0}
  output := []

/-- Observe terminal configurations without an additional transition. In particular,
after consuming `t` bits in `t` transitions, exhaustion can be detected at time `t`.
Setup and simulation transitions are accounted for separately from seed length
by the two budgets in `GeneratorTimeBound`. -/
def observe (data : InputData I A) (bits : BitString) (c : Configuration M) : RunState M :=
  match M.transition c.state (data.input[c.inputHead]?)
      (data.auxiliary[c.auxiliaryHead]?)
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | .accept => .halted (.accepted c.output)
  | .reject => .halted .rejected
  | .readRandom _ _ =>
    if c.randomHead < bits.length then .running c else .halted .exhausted
  | .step _ _ _ _ _ _ _ => .running c

def next (data : InputData I A) (bits : BitString) (c : Configuration M) : RunState M :=
  match M.transition c.state (data.input[c.inputHead]?)
      (data.auxiliary[c.auxiliaryHead]?)
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | .accept => .halted (.accepted c.output)
  | .reject => .halted .rejected
  | .readRandom onFalse onTrue =>
    match bits[c.randomHead]? with
    | none => .halted .exhausted
    | some b => .running { c with
        state := if b then onTrue else onFalse
        randomHead := c.randomHead + 1 }
  | .step nextState write workMove inputMove auxiliaryMove indexMove emit =>
    let newHead := workMove.onInt c.workHead
    .running { c with
      state := nextState
      inputHead := inputMove.onInput data.input.length c.inputHead
      auxiliaryHead := auxiliaryMove.onInput data.auxiliary.length c.auxiliaryHead
      indexHead := indexMove.onInput data.index c.indexHead
      workHead := newHead
      work := match write with
        | none => c.work
        | some symbol => Function.update c.work c.workHead (some symbol)
      visited := insert newHead c.visited
      output := match emit with
        | none => c.output
        | some symbol => c.output ++ [symbol] }

/-- Bounded simulation; halted runs stay halted as the clock increases. -/
def run (data : InputData I A) (bits : BitString) : ℕ → RunState M
  | 0 => M.observe data bits M.initialConfiguration
  | t + 1 => match run data bits t with
    | .halted result => .halted result
    | .running c => match M.next data bits c with
      | .halted result => .halted result
      | .running c' => M.observe data bits c'

def HaltsWithin (data : InputData I A) (bits : BitString) (t : ℕ) : Prop :=
  ∃ result, M.run data bits t = .halted result

def Halts (data : InputData I A) (bits : BitString) : Prop :=
  ∃ t, M.HaltsWithin data bits t

def Produces (data : InputData I A) (bits : BitString) (w : List O) : Prop :=
  ∃ t, M.run data bits t = .halted (.accepted w)

def Accepts (data : InputData I A) (bits : BitString) : Prop :=
  ∃ w, M.Produces data bits w

/-- A deterministic decision/verifier machine never requests random bits. -/
def Deterministic : Prop :=
  ∀ q input auxiliary index work,
    match M.transition q input auxiliary index work with
    | .readRandom _ _ => False
    | _ => True

/-- Worst-case time on *all* finite random tapes, including short tapes. -/
def TimeBound (data : InputData I A) (t : ℕ) : Prop :=
  ∀ bits, M.HaltsWithin data bits t

/-- Every visited work cell counts, including a cell entered immediately before
halting. The successor check includes configurations that `observe` halts on. -/
def SpaceBound (data : InputData I A) (s : ℕ) : Prop :=
  M.initialConfiguration.visited.card ≤ s ∧
  ∀ bits t c, M.run data bits t = .running c →
    c.visited.card ≤ s ∧
    ∀ c', M.next data bits c = .running c' → c'.visited.card ≤ s

/-- Once halted, extending the simulation clock cannot change the outcome. -/
theorem run_halted_add (data : InputData I A) (bits : BitString) (t : ℕ)
    (result : Outcome O) (h : M.run data bits t = .halted result) (s : ℕ) :
    M.run data bits (t + s) = .halted result := by
  induction s with
  | zero => simpa using h
  | succ s ih => simp [run, ih]

/-- Acceptance, explicit rejection, and exhaustion cannot occur on the same run. -/
theorem halted_outcome_unique (data : InputData I A) (bits : BitString)
    (t s : ℕ) (a b : Outcome O)
    (ha : M.run data bits t = .halted a) (hb : M.run data bits s = .halted b) :
    a = b := by
  have h₁ := M.run_halted_add data bits t a ha s
  have h₂ := M.run_halted_add data bits s b hb t
  rw [Nat.add_comm s t] at h₂
  exact RunState.halted.inj (h₁.symm.trans h₂)

end Machine

/-- Family input: unary size, optional read-only certificate, no ordinary input. -/
def generatorData (n : ℕ) (certificate : BitString := []) : InputData Unit Bool :=
  { index := n, auxiliary := certificate }

/-- Decision input: the word, with both auxiliary tapes empty. -/
def decisionData {α : Type} (w : Word α) : InputData α Bool :=
  { input := w }

/-- Verifier input: word and certificate on separate read-only tapes. -/
def verifierData {α : Type} (w : Word α) (c : BitString) : InputData α Bool :=
  { input := w, auxiliary := c }

end ComplexityOfGenerators
