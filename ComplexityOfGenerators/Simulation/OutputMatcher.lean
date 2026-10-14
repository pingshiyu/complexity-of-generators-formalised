import ComplexityOfGenerators.Foundations.RandomTape
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Infix

/-!
# Native streaming output comparison

The adapter compares a source's output to its ordinary input. One Boolean in
finite control records whether the output so far matches a prefix. Mismatches
do not interrupt simulation, so each source transition still costs exactly one
target transition. A final acceptance requires both a successful comparison and
the end of the input. No output word is stored in finite control.
-/

namespace ComplexityOfGenerators.Simulation

theorem matcher_prefix_snoc {α : Type} (out word : List α) (letter : α) :
    out ++ [letter] <+: word ↔ out <+: word ∧ word[min out.length word.length]? = some letter := by
  by_cases matched : out <+: word
  · obtain ⟨tail, rfl⟩ := matched
    rw [List.prefix_append_right_inj]
    have len : out.length ≤ (out ++ tail).length := by simp
    rw [Nat.min_eq_left len, List.getElem?_append_right (by omega), Nat.sub_self]
    cases tail <;> simp [List.cons_prefix_cons, eq_comm]
  · have impossible : ¬ out ++ [letter] <+: word := fun h => matched ((List.prefix_append _ _).trans h)
    simp [matched, impossible]

theorem matcher_finished {α : Type} (out word : List α) :
    out <+: word ∧ word[min out.length word.length]? = none ↔ out = word := by
  rw [List.getElem?_eq_none_iff]
  constructor
  · rintro ⟨matched, ended⟩
    exact matched.eq_of_length_le (by omega)
  · rintro rfl
    simp

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

local instance : DecidableEq α := Classical.decEq α

def matcherControl : (Fin M.states × Bool) ≃ Fin (Fintype.card (Fin M.states × Bool)) := Fintype.equivFin _

def matcherInstruction (matched : Bool) (input : Option α) : Instruction α M.states M.symbols →
    Instruction Unit (Fintype.card (Fin M.states × Bool)) M.symbols := by
  classical
  exact fun instruction => match instruction with
    | .accept => if matched && input.isNone then .accept else .reject
    | .reject => .reject
    | .readRandom no yes => .readRandom (matcherControl M (no, matched)) (matcherControl M (yes, matched))
    | .step next write work _ auxiliary index none =>
        .step (matcherControl M (next, matched)) write work .stay auxiliary index none
    | .step next write work _ auxiliary index (some letter) =>
        .step (matcherControl M (next, matched && decide (input = some letter))) write work .right auxiliary index none

def outputMatcher : Machine α Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (Fin M.states × Bool)
  symbols := M.symbols
  initial := matcherControl M (M.initial, true)
  transition := fun state input auxiliary index work =>
    let q := (matcherControl M).symm state
    matcherInstruction M q.2 input (M.transition q.1 none auxiliary index work)

def matcherSourceData (data : InputData α Bool) : InputData Unit Bool :=
  ⟨[], data.auxiliary, data.index⟩

def matcherConfiguration (word : List α) (source : Configuration M) : Configuration (outputMatcher M) := by
  classical
  exact {
    state := matcherControl M (source.state, decide (source.output <+: word))
    inputHead := min source.output.length word.length
    auxiliaryHead := source.auxiliaryHead
    indexHead := source.indexHead
    randomHead := source.randomHead
    workHead := source.workHead
    work := source.work
    visited := source.visited
    output := [] }

def matcherOutcome (word : List α) : Outcome α → Outcome Unit := by
  classical
  exact fun result => match result with
    | .accepted out => if out = word then .accepted [] else .rejected
    | .rejected => .rejected
    | .exhausted => .exhausted

def matcherResult (word : List α) : RunState M → RunState (outputMatcher M)
  | .running source => .running (matcherConfiguration M word source)
  | .halted result => .halted (matcherOutcome word result)

omit [Fintype α] in
theorem matcher_finished_bool (out word : List α) :
    (decide (out <+: word) && (word[min out.length word.length]?).isNone) = decide (out = word) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simpa using matcher_finished out word

omit [Fintype α] in
theorem matcher_prefix_snoc_bool (out word : List α) (letter : α) :
    (decide (out <+: word) && decide (word[min out.length word.length]? = some letter)) =
      decide (out ++ [letter] <+: word) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simpa using (matcher_prefix_snoc out word letter).symm

theorem outputMatcher_observe (data : InputData α Bool) (bits : BitString) (source : Configuration M) :
    (outputMatcher M).observe data bits (matcherConfiguration M data.input source) =
      matcherResult M data.input (M.observe (matcherSourceData data) bits source) := by
  classical
  simp only [Machine.observe, outputMatcher, matcherConfiguration, Equiv.symm_apply_apply,
    matcherSourceData, List.getElem?_nil]
  cases M.transition source.state none data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some () else none) (source.work source.workHead) with
  | accept =>
      simp only [matcherInstruction, matcher_finished_bool]
      by_cases same : source.output = data.input <;> simp [same, matcherResult, matcherOutcome]
  | reject => rfl
  | readRandom no yes => simp only [matcherInstruction]; split_ifs <;> rfl
  | step next write work input auxiliary index emit => cases emit <;> rfl

theorem outputMatcher_next (data : InputData α Bool) (bits : BitString) (source : Configuration M) :
    (outputMatcher M).next data bits (matcherConfiguration M data.input source) =
      matcherResult M data.input (M.next (matcherSourceData data) bits source) := by
  classical
  simp only [Machine.next, outputMatcher, matcherConfiguration, Equiv.symm_apply_apply,
    matcherSourceData, List.getElem?_nil]
  cases M.transition source.state none data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some () else none) (source.work source.workHead) with
  | accept =>
      simp only [matcherInstruction, matcher_finished_bool]
      by_cases same : source.output = data.input <;> simp [same, matcherResult, matcherOutcome]
  | reject => rfl
  | readRandom no yes =>
      simp only [matcherInstruction]
      cases bits[source.randomHead]? with
      | none => rfl
      | some bit => cases bit <;> rfl
  | step next write work input auxiliary index emit =>
      cases emit with
      | none =>
          simp only [matcherInstruction, matcherResult, matcherConfiguration, Move.onInput, Nat.min_self,
            Nat.min_assoc]
          cases write <;> rfl
      | some letter =>
          have head : min (min source.output.length data.input.length + 1) data.input.length =
              min (source.output ++ [letter]).length data.input.length := by simp; omega
          simp only [matcherInstruction, matcherResult, matcherConfiguration, Move.onInput, head,
            matcher_prefix_snoc_bool]
          cases write <;> rfl

/-- Clock-for-clock comparison, also valid on prepared work tapes. -/
theorem outputMatcher_runFrom (data : InputData α Bool) (bits : BitString)
    (source : Configuration M) (t : ℕ) :
    (outputMatcher M).runFrom data bits (matcherConfiguration M data.input source) t =
      matcherResult M data.input (M.runFrom (matcherSourceData data) bits source t) := by
  induction t with
  | zero => exact outputMatcher_observe M data bits source
  | succ t ih =>
      simp only [Machine.runFrom, ih]
      cases M.runFrom (matcherSourceData data) bits source t with
      | halted result => rfl
      | running current =>
          simp only [matcherResult, outputMatcher_next]
          cases M.next (matcherSourceData data) bits current with
          | halted result => rfl
          | running next => exact outputMatcher_observe M data bits next

theorem outputMatcher_run (data : InputData α Bool) (bits : BitString) (t : ℕ) :
    (outputMatcher M).run data bits t = matcherResult M data.input (M.run (matcherSourceData data) bits t) := by
  have initial : matcherConfiguration M data.input M.initialConfiguration = (outputMatcher M).initialConfiguration := by
    simp [matcherConfiguration, Machine.initialConfiguration, outputMatcher]
  simpa only [initial, Machine.runFrom_initial] using outputMatcher_runFrom M data bits M.initialConfiguration t

end

end ComplexityOfGenerators.Simulation
