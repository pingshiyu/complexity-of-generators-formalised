import ComplexityOfGenerators.Simulation.TranscriptReplaySoundness
import ComplexityOfGenerators.Simulation.PrimitiveOperations
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Reading a step transcript as the native random tape

This adapter consumes one padding bit and then one bit per source transition.
Ordinary steps ignore the bit; random instructions use it. Every nonterminal
source instruction costs exactly two native steps. This permits the existing
virtual-index recognizer and certificate-reader compilers to verify the same
certificates as `transcriptReplay`, without a new auxiliary-tape simulator.
-/

namespace ComplexityOfGenerators.Simulation

structure TranscriptAction (O : Type) (states symbols : ℕ) where
  state : Fin states
  write : Option (Fin symbols)
  work : Move
  input : Move
  index : Move
  emit : Option O

noncomputable section
local instance transcriptMoveFintype : Fintype Move := Fintype.ofFinite _
deriving instance Fintype for TranscriptAction

inductive RandomTranscriptPhase (O : Type) (states symbols : ℕ)
  | boot
  | source (q : Fin states)
  | execute (action : TranscriptAction O states symbols)
  deriving Fintype

set_option backward.isDefEq.respectTransparency false

variable {I O : Type} [Fintype O] (M : Machine I Bool O)

def randomTranscriptControl : RandomTranscriptPhase O M.states M.symbols ≃
    Fin (Fintype.card (RandomTranscriptPhase O M.states M.symbols)) := Fintype.equivFin _

def randomTranscriptResume (q : Fin M.states) : TranscriptAction O M.states M.symbols :=
  ⟨q, none, .stay, .stay, .stay, none⟩

def randomTranscriptInstruction : Instruction O M.states M.symbols →
    Instruction O (Fintype.card (RandomTranscriptPhase O M.states M.symbols)) M.symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom
      (randomTranscriptControl M (.execute (randomTranscriptResume M no)))
      (randomTranscriptControl M (.execute (randomTranscriptResume M yes)))
  | .step q write work input _ index emit =>
      let next := randomTranscriptControl M (.execute ⟨q, write, work, input, index, emit⟩)
      .readRandom next next

def randomTranscript : Machine I Bool O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  states := Fintype.card (RandomTranscriptPhase O M.states M.symbols)
  symbols := M.symbols
  initial := randomTranscriptControl M .boot
  transition := fun q input _ index work => match (randomTranscriptControl M).symm q with
    | .boot => .readRandom (randomTranscriptControl M (.source M.initial))
        (randomTranscriptControl M (.source M.initial))
    | .source state => randomTranscriptInstruction M (M.transition state input none index work)
    | .execute action => .step (randomTranscriptControl M (.source action.state)) action.write
        action.work action.input .stay action.index action.emit

def randomTranscriptConfiguration (c : Configuration M) (position : ℕ)
    (phase : RandomTranscriptPhase O M.states M.symbols := .source c.state) :
    Configuration (randomTranscript M) where
  state := randomTranscriptControl M phase
  inputHead := c.inputHead
  auxiliaryHead := 0
  indexHead := c.indexHead
  randomHead := position
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

/-- A helper action performs the original work/input/output operation; its
certificate bit has already been consumed by the preceding random read. -/
theorem randomTranscript_execute (input : List I) (n : ℕ) (bits : BitString)
    (c : Configuration M) (position : ℕ) (action : TranscriptAction O M.states M.symbols) :
    let data := transcriptSourceData input n
    let start := randomTranscriptConfiguration M c position (.execute action)
    let next := M.stepConfiguration data c action.state action.write action.work action.input .stay action.index action.emit
    (randomTranscript M).observe data bits start = .running start ∧
      (randomTranscript M).next data bits start = .running (randomTranscriptConfiguration M next position) := by
  dsimp only
  have table : (randomTranscript M).transition (randomTranscriptControl M (.execute action))
      input[c.inputHead]? none (if c.indexHead < n then some () else none) (c.work c.workHead) =
      .step (randomTranscriptControl M (.source action.state)) action.write action.work action.input
        .stay action.index action.emit := by simp [randomTranscript]
  refine ⟨(randomTranscript M).observe_step _ bits _ _ _ _ _ _ _ _ table, ?_⟩
  rw [(randomTranscript M).next_step _ bits _ _ _ _ _ _ _ _ table]
  cases action.write <;> cases action.emit <;> rfl

/-- Both random branches of an ordinary instruction execute the same action. -/
theorem randomTranscript_step (input : List I) (n : ℕ) (bits : BitString)
    (c : Configuration M) (position : ℕ) (bit : Bool) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work ordinary auxiliary index : Move) (emit : Option O)
    (action : M.transition c.state input[c.inputHead]? none
      (if c.indexHead < n then some () else none) (c.work c.workHead) =
      .step state write work ordinary auxiliary index emit)
    (lookup : bits[position]? = some bit) :
    (randomTranscript M).runFrom (transcriptSourceData input n) bits
      (randomTranscriptConfiguration M c position) 2 =
      (randomTranscript M).observe (transcriptSourceData input n) bits
        (randomTranscriptConfiguration M
          (M.stepConfiguration (transcriptSourceData input n) c state write work ordinary auxiliary index emit)
          (position + 1)) := by
  have available : position < bits.length := (List.getElem?_eq_some_iff.mp lookup).1
  have live : (randomTranscript M).observe (transcriptSourceData input n) bits
      (randomTranscriptConfiguration M c position) = .running (randomTranscriptConfiguration M c position) := by
    simp [Machine.observe, randomTranscript, randomTranscriptConfiguration, transcriptSourceData,
      randomTranscriptInstruction, action, available]
  have next : (randomTranscript M).next (transcriptSourceData input n) bits
      (randomTranscriptConfiguration M c position) = .running
        (randomTranscriptConfiguration M c (position + 1) (.execute ⟨state, write, work, ordinary, index, emit⟩)) := by
    simp [Machine.next, randomTranscript, randomTranscriptConfiguration, transcriptSourceData,
      randomTranscriptInstruction, action, lookup]
  have helper := randomTranscript_execute M input n bits c (position + 1) ⟨state, write, work, ordinary, index, emit⟩
  rw [(randomTranscript M).runFrom_shift _ bits _ _ live next 1,
    (randomTranscript M).runFrom_shift _ bits _ _ helper.1 helper.2 0]
  rfl

theorem randomTranscript_random (input : List I) (n : ℕ) (bits : BitString)
    (c : Configuration M) (position : ℕ) (bit : Bool) (no yes : Fin M.states)
    (inputBound : c.inputHead ≤ input.length) (indexBound : c.indexHead ≤ n) (head : c.workHead ∈ c.visited)
    (action : M.transition c.state input[c.inputHead]? none
      (if c.indexHead < n then some () else none) (c.work c.workHead) = .readRandom no yes)
    (lookup : bits[position]? = some bit) :
    (randomTranscript M).runFrom (transcriptSourceData input n) bits
      (randomTranscriptConfiguration M c position) 2 =
      (randomTranscript M).observe (transcriptSourceData input n) bits
        (randomTranscriptConfiguration M {c with state := if bit then yes else no, randomHead := 0} (position + 1)) := by
  have available : position < bits.length := (List.getElem?_eq_some_iff.mp lookup).1
  have live : (randomTranscript M).observe (transcriptSourceData input n) bits
      (randomTranscriptConfiguration M c position) = .running (randomTranscriptConfiguration M c position) := by
    simp [Machine.observe, randomTranscript, randomTranscriptConfiguration, transcriptSourceData,
      randomTranscriptInstruction, action, available]
  have next : (randomTranscript M).next (transcriptSourceData input n) bits
      (randomTranscriptConfiguration M c position) = .running
        (randomTranscriptConfiguration M c (position + 1)
          (.execute (randomTranscriptResume M (if bit then yes else no)))) := by
    cases bit <;> simp [Machine.next, randomTranscript, randomTranscriptConfiguration, transcriptSourceData,
      randomTranscriptInstruction, action, lookup]
  have helper := randomTranscript_execute M input n bits c (position + 1) (randomTranscriptResume M (if bit then yes else no))
  rw [(randomTranscript M).runFrom_shift _ bits _ _ live next 1,
    (randomTranscript M).runFrom_shift _ bits _ _ helper.1 helper.2 0]
  simp [Machine.runFrom, randomTranscriptConfiguration, Machine.stepConfiguration, transcriptSourceData,
    randomTranscriptResume, Move.onInput, Move.onInt, Nat.min_eq_left inputBound,
    Nat.min_eq_left indexBound, Finset.insert_eq_of_mem head]

end
end ComplexityOfGenerators.Simulation
