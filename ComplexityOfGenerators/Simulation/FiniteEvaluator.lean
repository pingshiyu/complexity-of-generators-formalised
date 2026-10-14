import ComplexityOfGenerators.Foundations.RandomTape
import Mathlib.Computability.Primrec.List

/-!
# A finite-data implementation of the native evaluator

Native configurations use a function for the two-way work tape. Every reachable
tape nevertheless has finite support. The evaluator below stores writes in a
finite association list, newest first, and records visited cells in a finite
list. Its correspondence with the original evaluator includes output, random
head, and visited-cell accounting. No machine model is redefined.
-/

namespace ComplexityOfGenerators.Simulation

variable {I A O : Type} (M : Machine I A O)

theorem configuration_ext {c d : Configuration M}
    (state : c.state = d.state) (inputHead : c.inputHead = d.inputHead)
    (auxiliaryHead : c.auxiliaryHead = d.auxiliaryHead) (indexHead : c.indexHead = d.indexHead)
    (randomHead : c.randomHead = d.randomHead) (workHead : c.workHead = d.workHead)
    (work : c.work = d.work) (visited : c.visited = d.visited) (output : c.output = d.output) :
    c = d := by
  cases c
  cases d
  cases state
  cases inputHead
  cases auxiliaryHead
  cases indexHead
  cases randomHead
  cases workHead
  cases work
  cases visited
  cases output
  rfl

structure FiniteConfiguration where
  state : Fin M.states
  inputHead : ℕ
  auxiliaryHead : ℕ
  indexHead : ℕ
  randomHead : ℕ
  workHead : ℤ
  work : List (ℤ × Fin M.symbols)
  visited : List ℤ
  output : List O

/-- A standard product encoding; the tape is a finite list, not an encoded
arbitrary function on integers. -/
abbrev ConfigurationCode := Fin M.states × ℕ × ℕ × ℕ × ℕ × ℤ ×
  List (ℤ × Fin M.symbols) × List ℤ × List O

def finiteConfigurationEquiv : FiniteConfiguration M ≃ ConfigurationCode M where
  toFun c := ⟨c.state, c.inputHead, c.auxiliaryHead, c.indexHead, c.randomHead,
    c.workHead, c.work, c.visited, c.output⟩
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1,
    c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable O] : Primcodable (FiniteConfiguration M) :=
  Primcodable.ofEquiv (ConfigurationCode M) (finiteConfigurationEquiv M)

def FiniteConfiguration.denote (c : FiniteConfiguration M) : Configuration M where
  state := c.state
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := fun i => c.work.lookup i
  visited := c.visited.toFinset
  output := c.output

def finiteInitial : FiniteConfiguration M := ⟨M.initial, 0, 0, 0, 0, 0, [], [0], []⟩

@[simp] theorem finiteInitial_denote : (finiteInitial M).denote = M.initialConfiguration := rfl

/-- `inl` is running; `inr (inl word)` is accepting; `inr (inr false)` is
explicit rejection; `inr (inr true)` is random-tape exhaustion. -/
abbrev FiniteResult := FiniteConfiguration M ⊕ (List O ⊕ Bool)

def denoteFiniteResult : FiniteResult M → RunState M
  | .inl c => .running c.denote
  | .inr (.inl word) => .halted (.accepted word)
  | .inr (.inr false) => .halted .rejected
  | .inr (.inr true) => .halted .exhausted

def finiteInstruction (data : InputData I A) (c : FiniteConfiguration M) :
    Instruction O M.states M.symbols :=
  M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work.lookup c.workHead)

def finiteObserve (data : InputData I A) (bits : BitString) (c : FiniteConfiguration M) :
    FiniteResult M :=
  match finiteInstruction M data c with
  | .accept => .inr (.inl c.output)
  | .reject => .inr (.inr false)
  | .readRandom _ _ => if c.randomHead < bits.length then .inl c else .inr (.inr true)
  | .step _ _ _ _ _ _ _ => .inl c

def finiteNext (data : InputData I A) (bits : BitString) (c : FiniteConfiguration M) :
    FiniteResult M :=
  match finiteInstruction M data c with
  | .accept => .inr (.inl c.output)
  | .reject => .inr (.inr false)
  | .readRandom onFalse onTrue =>
    match bits[c.randomHead]? with
    | none => .inr (.inr true)
    | some b => .inl {c with
        state := if b then onTrue else onFalse
        randomHead := c.randomHead + 1}
  | .step state write workMove inputMove auxiliaryMove indexMove emit =>
    .inl {c with
      state := state
      inputHead := inputMove.onInput data.input.length c.inputHead
      auxiliaryHead := auxiliaryMove.onInput data.auxiliary.length c.auxiliaryHead
      indexHead := indexMove.onInput data.index c.indexHead
      workHead := workMove.onInt c.workHead
      work := match write with
        | none => c.work
        | some symbol => (c.workHead, symbol) :: c.work
      visited := workMove.onInt c.workHead :: c.visited
      output := match emit with
        | none => c.output
        | some symbol => c.output ++ [symbol]}

def finiteRun (data : InputData I A) (bits : BitString) : ℕ → FiniteResult M
  | 0 => finiteObserve M data bits (finiteInitial M)
  | t + 1 => match finiteRun data bits t with
    | .inr result => .inr result
    | .inl c => match finiteNext M data bits c with
      | .inr result => .inr result
      | .inl d => finiteObserve M data bits d

theorem finiteObserve_denote (data : InputData I A) (bits : BitString)
    (c : FiniteConfiguration M) :
    denoteFiniteResult M (finiteObserve M data bits c) = M.observe data bits c.denote := by
  have instruction : M.transition c.denote.state data.input[c.denote.inputHead]?
      data.auxiliary[c.denote.auxiliaryHead]?
      (if c.denote.indexHead < data.index then some () else none)
      (c.denote.work c.denote.workHead) = finiteInstruction M data c := rfl
  simp only [finiteObserve, Machine.observe, instruction]
  cases finiteInstruction M data c <;> try rfl
  by_cases available : c.randomHead < bits.length <;>
    simp [available, FiniteConfiguration.denote, denoteFiniteResult]

theorem finiteNext_denote (data : InputData I A) (bits : BitString)
    (c : FiniteConfiguration M) :
    denoteFiniteResult M (finiteNext M data bits c) = M.next data bits c.denote := by
  have instruction : M.transition c.denote.state data.input[c.denote.inputHead]?
      data.auxiliary[c.denote.auxiliaryHead]?
      (if c.denote.indexHead < data.index then some () else none)
      (c.denote.work c.denote.workHead) = finiteInstruction M data c := rfl
  simp only [finiteNext, Machine.next, instruction]
  cases finiteInstruction M data c with
  | accept => rfl
  | reject => rfl
  | readRandom onFalse onTrue =>
      simp only [FiniteConfiguration.denote]
      cases bits[c.randomHead]? <;> rfl
  | step state write workMove inputMove auxiliaryMove indexMove emit =>
      cases write <;> dsimp only [denoteFiniteResult, FiniteConfiguration.denote] <;> congr 1
      all_goals apply configuration_ext M <;> try rfl
      all_goals try { simp only [List.toFinset_cons] }
      funext i
      by_cases same : i = c.workHead
      · subst i
        simp
      · have different : (i == c.workHead) = false := beq_eq_false_iff_ne.mpr same
        simp [List.lookup_cons, same, different]

/-- Exact equality at every clock, including exhausted and rejected runs.
This proves the evaluator faithful without any halting assumption. -/
theorem finiteRun_denote (data : InputData I A) (bits : BitString) (t : ℕ) :
    denoteFiniteResult M (finiteRun M data bits t) = M.run data bits t := by
  induction t with
  | zero => exact finiteObserve_denote M data bits (finiteInitial M)
  | succ t ih =>
      rw [Machine.run, ← ih]
      rw [finiteRun]
      cases finiteRun M data bits t with
      | inr result => cases result with
          | inl word => rfl
          | inr b => cases b <;> rfl
      | inl c =>
          dsimp only [denoteFiniteResult]
          rw [← finiteNext_denote M data bits c]
          cases finiteNext M data bits c with
          | inr result => cases result with
              | inl word => rfl
              | inr b => cases b <;> rfl
          | inl d => exact finiteObserve_denote M data bits d

theorem finiteRun_accepts_iff (data : InputData I A) (bits : BitString) (t : ℕ) (word : List O) :
    finiteRun M data bits t = .inr (.inl word) ↔
      M.run data bits t = .halted (.accepted word) := by
  rw [← finiteRun_denote]
  cases finiteRun M data bits t with
  | inl c => simp [denoteFiniteResult]
  | inr result => cases result with
      | inl output => simp [denoteFiniteResult]
      | inr b => cases b <;> simp [denoteFiniteResult]

end ComplexityOfGenerators.Simulation
