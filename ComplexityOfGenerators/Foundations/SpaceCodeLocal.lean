import ComplexityOfGenerators.Foundations.SpaceCodeExecution

/-! Local, fieldwise characterisation of configuration-graph edges. This is
the interface between the native base-test routines and the bounded graph:
control, observations, head moves, and the single permitted tape-cell update. -/

namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O)

private theorem coordinate_bound (s : ℕ) (i : Fin (2 * s + 1)) :
    ((i.val : ℤ) - s).natAbs ≤ s := by
  have := i.isLt
  generalize coordinate : (i.val : ℤ) - s = value
  cases value <;> simp_all <;> omega

/-- The indexed cell of a decoded tape is exactly the corresponding finite
array entry, at every position in the represented window. -/
theorem decodeSpaceCode_cell {data : InputData I A} {s : ℕ}
    (code : M.SpaceCode data s) (i : Fin (2 * s + 1)) :
    (M.decodeSpaceCode code).work ((i.val : ℤ) - s) = code.2.2.2.2.2 i := by
  simp only [decodeSpaceCode, coordinate_bound s i, ↓reduceDIte]
  apply congrArg code.2.2.2.2.2
  apply Fin.ext
  simp

/-- Reading the work head involves a single entry of the finite array. -/
theorem decodeSpaceCode_workHead {data : InputData I A} {s : ℕ}
    (code : M.SpaceCode data s) :
    (M.decodeSpaceCode code).work (M.decodeSpaceCode code).workHead =
      code.2.2.2.2.2 code.2.2.2.2.1 := M.decodeSpaceCode_cell code _

def spaceCodeInstruction (data : InputData I A) (s : ℕ) (code : M.SpaceCode data s) :
    Instruction O M.states M.symbols :=
  M.transition code.1 data.input[code.2.1.val]? data.auxiliary[code.2.2.1.val]?
    (if code.2.2.2.1.val < data.index then some () else none) (code.2.2.2.2.2 code.2.2.2.2.1)

theorem spaceCodeInstruction_eq (data : InputData I A) (s : ℕ) (code : M.SpaceCode data s) :
    M.spaceCodeInstruction data s code =
      M.transition (M.decodeSpaceCode code).state data.input[(M.decodeSpaceCode code).inputHead]?
        data.auxiliary[(M.decodeSpaceCode code).auxiliaryHead]?
        (if (M.decodeSpaceCode code).indexHead < data.index then some () else none)
        ((M.decodeSpaceCode code).work (M.decodeSpaceCode code).workHead) := by
  rw [M.decodeSpaceCode_workHead]
  rfl

/-- Equality of decoded work tapes is equality of the finite arrays. -/
theorem decodeSpaceCode_work_eq_iff {data : InputData I A} {s : ℕ}
    (a b : M.SpaceCode data s) :
    (M.decodeSpaceCode a).work = (M.decodeSpaceCode b).work ↔ a.2.2.2.2.2 = b.2.2.2.2.2 := by
  constructor
  · intro eq
    funext i
    simpa only [M.decodeSpaceCode_cell] using congrFun eq ((i.val : ℤ) - s)
  · intro eq
    funext i
    simp only [decodeSpaceCode, eq]

/-- Updating one finite cell commutes with decoding to the infinite, blank
outside tape. This includes replacing a cell by its previous value. -/
theorem decodeSpaceCode_work_update_iff {data : InputData I A} {s : ℕ}
    (a b : M.SpaceCode data s) (cell : Option (Fin M.symbols)) :
    (M.decodeSpaceCode b).work =
      Function.update (M.decodeSpaceCode a).work (M.decodeSpaceCode a).workHead cell ↔
    b.2.2.2.2.2 = Function.update a.2.2.2.2.2 a.2.2.2.2.1 cell := by
  constructor
  · intro eq
    funext i
    have atCell := congrFun eq ((i.val : ℤ) - s)
    rw [M.decodeSpaceCode_cell] at atCell
    by_cases same : i = a.2.2.2.2.1
    · subst i
      simpa [decodeSpaceCode, Function.update_apply] using atCell
    · have different : ((i.val : ℤ) - s) ≠ (M.decodeSpaceCode a).workHead := by
        intro eq
        apply same
        apply Fin.ext
        change (i.val : ℤ) - s = (a.2.2.2.2.1.val : ℤ) - s at eq
        omega
      simpa only [Function.update_of_ne different, M.decodeSpaceCode_cell,
        Function.update_of_ne same] using atCell
  · intro eq
    funext i
    by_cases same : i = (M.decodeSpaceCode a).workHead
    · subst i
      rw [Function.update_self]
      change (M.decodeSpaceCode b).work ((a.2.2.2.2.1.val : ℤ) - s) = cell
      rw [M.decodeSpaceCode_cell, eq, Function.update_self]
    · rw [Function.update_of_ne same]
      by_cases inside : i.natAbs ≤ s
      · simp only [decodeSpaceCode, inside, ↓reduceDIte, eq]
        apply Function.update_of_ne
        intro equal
        apply same
        have coords := congrArg (fun j : Fin (2 * s + 1) => (j.val : ℤ) - s) equal
        change ((i + (s : ℤ)).toNat : ℤ) - s = (a.2.2.2.2.1.val : ℤ) - s at coords
        have lower : -(s : ℤ) ≤ i := by
          cases i <;> simp_all <;> omega
        change i = (a.2.2.2.2.1.val : ℤ) - s
        omega
      · simp only [decodeSpaceCode, inside, ↓reduceDIte]

/-- The deterministic instruction case is six local field comparisons. No
history, random cursor, output buffer, or infinite-tape equality is needed. -/
theorem spaceCodeAdvance_step_iff (data : InputData I A) (s : ℕ) (choice : Bool)
    (a b : M.SpaceCode data s) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (action : M.spaceCodeInstruction data s a = .step state write work input auxiliary index emit) :
    M.spaceCodeAdvance data s choice a = some b ↔
      b.1 = state ∧
      b.2.1.val = input.onInput data.input.length a.2.1.val ∧
      b.2.2.1.val = auxiliary.onInput data.auxiliary.length a.2.2.1.val ∧
      b.2.2.2.1.val = index.onInput data.index a.2.2.2.1.val ∧
      (b.2.2.2.2.1.val : ℤ) - s = work.onInt ((a.2.2.2.2.1.val : ℤ) - s) ∧
      b.2.2.2.2.2 = Function.update a.2.2.2.2.2 a.2.2.2.2.1
        (match write with | none => a.2.2.2.2.2 a.2.2.2.2.1 | some symbol => some symbol) := by
  rw [M.spaceCodeAdvance_eq_some]
  rw [M.spaceCodeInstruction_eq] at action
  simp only [DecisionView.advance, action, Option.some.injEq, DecisionView.ext_iff]
  cases write with
  | none =>
      dsimp only
      simp only [Function.update_eq_self]
      rw [M.decodeSpaceCode_work_eq_iff]
      simp only [decodeSpaceCode]
      tauto
  | some symbol =>
      have workEq := M.decodeSpaceCode_work_update_iff a b (some symbol)
      have workEq' : Function.update (M.decodeSpaceCode a).work (M.decodeSpaceCode a).workHead (some symbol) =
          (M.decodeSpaceCode b).work ↔
          b.2.2.2.2.2 = Function.update a.2.2.2.2.2 a.2.2.2.2.1 (some symbol) := eq_comm.trans workEq
      rw [workEq']
      simp only [decodeSpaceCode]
      tauto

/-- A random instruction changes only the finite control state. -/
theorem spaceCodeAdvance_random_iff (data : InputData I A) (s : ℕ) (choice : Bool)
    (a b : M.SpaceCode data s) (no yes : Fin M.states)
    (action : M.spaceCodeInstruction data s a = .readRandom no yes) :
    M.spaceCodeAdvance data s choice a = some b ↔
      b.1 = (if choice then yes else no) ∧ b.2 = a.2 := by
  rw [M.spaceCodeAdvance_eq_some]
  rw [M.spaceCodeInstruction_eq] at action
  simp only [DecisionView.advance, action, Option.some.injEq, DecisionView.ext_iff]
  rw [M.decodeSpaceCode_work_eq_iff]
  simp [decodeSpaceCode, Prod.ext_iff, Fin.ext_iff, eq_comm]

/-- Halting instructions contribute no graph edge. -/
theorem spaceCodeAdvance_halt (data : InputData I A) (s : ℕ) (choice : Bool)
    (a : M.SpaceCode data s)
    (action : M.spaceCodeInstruction data s a = .accept ∨ M.spaceCodeInstruction data s a = .reject) :
    M.spaceCodeAdvance data s choice a = none := by
  have stopped : (M.decodeSpaceCode a).advance M data choice = none := by
    rcases action with action | action <;>
      rw [M.spaceCodeInstruction_eq] at action <;>
      simp only [DecisionView.advance, action]
  cases result : M.spaceCodeAdvance data s choice a with
  | none => rfl
  | some b =>
      have step := (M.spaceCodeAdvance_eq_some data s choice a b).mp result
      rw [stopped] at step
      cases step

theorem spaceCodeAccepting_eq (data : InputData I A) (s : ℕ) (a : M.SpaceCode data s) :
    M.spaceCodeAccepting data s a =
      (match M.spaceCodeInstruction data s a with | .accept => true | _ => false) := by
  rw [M.spaceCodeInstruction_eq]
  rfl

end ComplexityOfGenerators.Machine
