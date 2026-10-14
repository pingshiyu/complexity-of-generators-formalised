import ComplexityOfGenerators.Foundations.SpaceBounds
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite configurations for space-bounded recognition

The random cursor, output history, and visited-cell history are not part of a
decision configuration: none is inspected by the transition table. Keeping the
random cursor would incorrectly make the configuration space infinite. The work
tape is represented by a finite window, justified by `TapeGeometry` rather than
an assumption about running time. This module proves the encoding faithful and
counts its possible values; it does not assert a machine simulation of Savitch.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

@[ext] structure DecisionView where
  state : Fin M.states
  inputHead : ℕ
  auxiliaryHead : ℕ
  indexHead : ℕ
  workHead : ℤ
  work : ℤ → Option (Fin M.symbols)

def decisionView (c : Configuration M) : M.DecisionView :=
  ⟨c.state, c.inputHead, c.auxiliaryHead, c.indexHead, c.workHead, c.work⟩

/-- One source transition after erasing unobservable histories. Randomness is
supplied only to `readRandom`; this is the native choice convention. -/
def DecisionView.advance (data : InputData I A) (choice : Bool) (c : M.DecisionView) :
    Option M.DecisionView :=
  match M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | .accept | .reject => none
  | .readRandom no yes => some {c with state := if choice then yes else no}
  | .step state write work input auxiliary index _ => some {
      state := state
      inputHead := input.onInput data.input.length c.inputHead
      auxiliaryHead := auxiliary.onInput data.auxiliary.length c.auxiliaryHead
      indexHead := index.onInput data.index c.indexHead
      workHead := work.onInt c.workHead
      work := match write with
        | none => c.work
        | some symbol => Function.update c.work c.workHead (some symbol) }

/-- Erasing a real transition gives an edge of the decision configuration
graph. In particular, output or visit histories cannot change a future edge. -/
theorem next_decisionView (data : InputData I A) (bits : BitString) (c d : Configuration M)
    (step : M.next data bits c = .running d) :
    ∃ choice, (M.decisionView c).advance M data choice = some (M.decisionView d) := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp [next, action] at step
  | reject => simp [next, action] at step
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [next, action, lookup] at step
      | some bit =>
          simp only [next, action, lookup, RunState.running.injEq] at step
          subst d
          refine ⟨bit, ?_⟩
          dsimp only [DecisionView.advance, decisionView]
          rw [action]
  | step state write work input auxiliary index emit =>
      rw [M.next_step data bits c state write work input auxiliary index emit action] at step
      cases step
      refine ⟨false, ?_⟩
      dsimp only [DecisionView.advance, decisionView, stepConfiguration]
      rw [action]
      rfl

structure DecisionView.Bounded (data : InputData I A) (s : ℕ) (c : M.DecisionView) : Prop where
  inputHead : c.inputHead ≤ data.input.length
  auxiliaryHead : c.auxiliaryHead ≤ data.auxiliary.length
  indexHead : c.indexHead ≤ data.index
  workHead : c.workHead.natAbs ≤ s
  blank : ∀ i : ℤ, s < i.natAbs → c.work i = none

/-- Heads, control state, and the `2s+1` work cells in `[-s,s]`. -/
abbrev SpaceCode (data : InputData I A) (s : ℕ) :=
  Fin M.states × Fin (data.input.length + 1) × Fin (data.auxiliary.length + 1) ×
    Fin (data.index + 1) × Fin (2 * s + 1) × (Fin (2 * s + 1) → Option (Fin M.symbols))

private theorem abs_bounds (i : ℤ) (s : ℕ) (bound : i.natAbs ≤ s) :
    -(s : ℤ) ≤ i ∧ i ≤ (s : ℤ) := by
  cases i <;> simp_all <;> omega

private theorem window_index_lt (i : ℤ) (s : ℕ) (bound : i.natAbs ≤ s) :
    (i + (s : ℤ)).toNat < 2 * s + 1 := by
  have := abs_bounds i s bound
  omega

private theorem window_index_coordinate (i : ℤ) (s : ℕ) (bound : i.natAbs ≤ s) :
    ((i + (s : ℤ)).toNat : ℤ) - s = i := by
  have := abs_bounds i s bound
  omega

def DecisionView.encode {data : InputData I A} {s : ℕ} (c : M.DecisionView)
    (h : c.Bounded M data s) : M.SpaceCode data s :=
  ⟨c.state, ⟨c.inputHead, Nat.lt_succ_of_le h.inputHead⟩,
    ⟨c.auxiliaryHead, Nat.lt_succ_of_le h.auxiliaryHead⟩,
    ⟨c.indexHead, Nat.lt_succ_of_le h.indexHead⟩,
    ⟨(c.workHead + (s : ℤ)).toNat, window_index_lt _ _ h.workHead⟩,
    fun i => c.work ((i.val : ℤ) - s)⟩

def decodeSpaceCode {data : InputData I A} {s : ℕ} (code : M.SpaceCode data s) : M.DecisionView where
  state := code.1
  inputHead := code.2.1.val
  auxiliaryHead := code.2.2.1.val
  indexHead := code.2.2.2.1.val
  workHead := (code.2.2.2.2.1.val : ℤ) - s
  work := fun i => if bound : i.natAbs ≤ s then
    code.2.2.2.2.2 ⟨(i + (s : ℤ)).toNat, window_index_lt i s bound⟩ else none

/-- Decoding recovers the entire infinite tape, since everything beyond the
encoded window is proved blank. No quotient by an unproved invariant is used. -/
theorem DecisionView.decode_encode {data : InputData I A} {s : ℕ} (c : M.DecisionView)
    (h : c.Bounded M data s) : M.decodeSpaceCode (c.encode M h) = c := by
  apply DecisionView.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact window_index_coordinate _ _ h.workHead
  · funext i
    change (if bound : i.natAbs ≤ s then
      c.work (((i + (s : ℤ)).toNat : ℤ) - s) else none) = c.work i
    by_cases inside : i.natAbs ≤ s
    · simp only [inside, ↓reduceDIte, window_index_coordinate i s inside]
    · simp only [inside, ↓reduceDIte]
      exact (h.blank i (by omega)).symm

theorem DecisionView.encode_injective (data : InputData I A) (s : ℕ) :
    Function.Injective (fun c : {c : M.DecisionView // c.Bounded M data s} => c.val.encode M c.property) := by
  intro c d same
  apply Subtype.ext
  have decoded := congrArg (M.decodeSpaceCode (data := data) (s := s)) same
  simpa only [DecisionView.decode_encode] using decoded

/-- An explicit finite type of all bounded decision configurations. -/
noncomputable instance boundedDecisionView_fintype (data : InputData I A) (s : ℕ) :
    Fintype {c : M.DecisionView // c.Bounded M data s} :=
  Fintype.ofInjective _ (DecisionView.encode_injective M data s)

theorem spaceCode_card (data : InputData I A) (s : ℕ) :
    Fintype.card (M.SpaceCode data s) =
      M.states * (data.input.length + 1) * (data.auxiliary.length + 1) *
        (data.index + 1) * (2 * s + 1) * (M.symbols + 1) ^ (2 * s + 1) := by
  simp only [SpaceCode, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_option]
  simp only [Nat.mul_assoc]

theorem boundedDecisionView_card_le (data : InputData I A) (s : ℕ) :
    Fintype.card {c : M.DecisionView // c.Bounded M data s} ≤
      M.states * (data.input.length + 1) * (data.auxiliary.length + 1) *
        (data.index + 1) * (2 * s + 1) * (M.symbols + 1) ^ (2 * s + 1) := by
  rw [← M.spaceCode_card data s]
  exact Fintype.card_le_of_injective _ (DecisionView.encode_injective M data s)

/-- For decision inputs, the number of configuration codes is singly
exponential in the input length and work-space bound. -/
theorem decisionSpaceCode_card_le (word : List I) (s : ℕ) :
    Fintype.card (M.SpaceCode {input := word} s) ≤
      2 ^ (M.states + (word.length + 1) + (2 * s + 1) + (M.symbols + 1) * (2 * s + 1)) := by
  rw [M.spaceCode_card]
  simp only [List.length_nil, Nat.zero_add, Nat.mul_one]
  calc
    M.states * (word.length + 1) * (2 * s + 1) * (M.symbols + 1) ^ (2 * s + 1) ≤
        2 ^ M.states * 2 ^ (word.length + 1) * 2 ^ (2 * s + 1) *
          (2 ^ (M.symbols + 1)) ^ (2 * s + 1) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul
          (Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le) Nat.lt_two_pow_self.le
      · exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = _ := by simp only [pow_add, pow_mul, Nat.mul_assoc]

/-- Every running configuration of a space-bounded computation has a code in
the same finite type, regardless of elapsed time or random-tape length. -/
theorem SpaceBound.decisionView_bounded {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) (bits : BitString) (t : ℕ) (c : Configuration M)
    (running : M.run data bits t = .running c) : (M.decisionView c).Bounded M data s := by
  have time := M.run_configurationBound data bits t c running
  have geometry := M.run_geometry data bits t c running
  have visited := (space.2 bits t c running).1
  refine ⟨time.inputHead, time.auxiliaryHead, time.indexHead, ?_, ?_⟩
  · have := geometry.workHead_bound M
    change c.workHead.natAbs ≤ s
    omega
  · intro i outside
    exact geometry.blank_outside_window M visited i outside.le

/-- The configuration entered on the last transition is covered as well, even
though a subsequent observation returns a halted outcome rather than this state. -/
theorem SpaceBound.next_decisionView_bounded {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) (bits : BitString) (t : ℕ) (c d : Configuration M)
    (running : M.run data bits t = .running c) (step : M.next data bits c = .running d) :
    (M.decisionView d).Bounded M data s := by
  have time := M.next_executionBound data bits t c (M.run_configurationBound data bits t c running)
  rw [step] at time
  have geometry := M.next_geometry data bits c d (M.run_geometry data bits t c running) step
  have visited := (space.2 bits t c running).2 d step
  refine ⟨time.inputHead, time.auxiliaryHead, time.indexHead, ?_, ?_⟩
  · have := geometry.workHead_bound M
    change d.workHead.natAbs ≤ s
    omega
  · intro i outside
    exact geometry.blank_outside_window M visited i outside.le

end ComplexityOfGenerators.Machine
