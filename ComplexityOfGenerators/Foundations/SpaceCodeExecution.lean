import ComplexityOfGenerators.Foundations.SpaceReachability

/-!
# Executable transitions on finite space codes

The configuration graph can be explored using finite arrays and bounded
coordinates. No decision procedure for equality of infinite work tapes is
needed. A transition leaving the represented work window is discarded; on a
space-bounded computation, the reachability proofs show that this never removes
a reachable edge.
-/

namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

variable {I A O : Type} (M : Machine I A O)

private theorem code_coordinate_bound (s : ℕ) (i : Fin (2 * s + 1)) :
    ((i.val : ℤ) - s).natAbs ≤ s := by
  have := i.isLt
  generalize coordinate : (i.val : ℤ) - s = value
  cases value <;> simp_all <;> omega

theorem decodeSpaceCode_bounded (data : InputData I A) (s : ℕ) (code : M.SpaceCode data s) :
    (M.decodeSpaceCode code).Bounded M data s := by
  refine ⟨Nat.le_of_lt_succ code.2.1.isLt, Nat.le_of_lt_succ code.2.2.1.isLt,
    Nat.le_of_lt_succ code.2.2.2.1.isLt, code_coordinate_bound s code.2.2.2.2.1, ?_⟩
  intro i outside
  simp only [decodeSpaceCode, show ¬ i.natAbs ≤ s by omega, ↓reduceDIte]

/-- All finite codes decode canonically, not just those reached during a run. -/
theorem encode_decodeSpaceCode (data : InputData I A) (s : ℕ) (code : M.SpaceCode data s) :
    (M.decodeSpaceCode code).encode M (M.decodeSpaceCode_bounded data s code) = code := by
  rcases code with ⟨state, input, auxiliary, index, head, cells⟩
  simp only [DecisionView.encode, decodeSpaceCode]
  congr 1
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply Fin.ext
    simp
  · funext i
    have inside := code_coordinate_bound s i
    simp only [inside, ↓reduceDIte]
    congr 1
    apply Fin.ext
    simp

/-- The only potentially unbounded field of a successor is its work head.
Writing inside the old window cannot change any cell outside that window. -/
theorem DecisionView.advance_bounded {data : InputData I A} {s : ℕ}
    {c d : M.DecisionView} (bounded : c.Bounded M data s) (choice : Bool)
    (step : c.advance M data choice = some d) (head : d.workHead.natAbs ≤ s) :
    d.Bounded M data s := by
  unfold DecisionView.advance at step
  split at step
  · cases step
  · cases step
  · cases Option.some.inj step
    exact ⟨bounded.inputHead, bounded.auxiliaryHead, bounded.indexHead, head, bounded.blank⟩
  · rename_i state write work input auxiliary index emit action
    cases Option.some.inj step
    refine ⟨input.onInput_le _ _ bounded.inputHead,
      auxiliary.onInput_le _ _ bounded.auxiliaryHead,
      index.onInput_le _ _ bounded.indexHead, head, ?_⟩
    intro i outside
    have different : i ≠ c.workHead := by
      intro same
      rw [same] at outside
      exact (Nat.not_lt_of_ge bounded.workHead) outside
    cases write with
    | none => exact bounded.blank i outside
    | some symbol =>
        simp only [Function.update_of_ne different]
        exact bounded.blank i outside

/-- One effective transition on the finite encoding. A missing result means
that the source halts or the next head would leave the represented window. -/
def spaceCodeAdvance (data : InputData I A) (s : ℕ) (choice : Bool)
    (code : M.SpaceCode data s) : Option (M.SpaceCode data s) :=
  match step : (M.decodeSpaceCode code).advance M data choice with
  | none => none
  | some next =>
      if head : next.workHead.natAbs ≤ s then
        some (next.encode M (DecisionView.advance_bounded M (M.decodeSpaceCode_bounded data s code) choice step head))
      else none

/-- The encoded step is exactly the original decision-view transition on
bounded source and target vertices. -/
theorem spaceCodeAdvance_eq_some (data : InputData I A) (s : ℕ) (choice : Bool)
    (source target : M.SpaceCode data s) :
    M.spaceCodeAdvance data s choice source = some target ↔
      (M.decodeSpaceCode source).advance M data choice = some (M.decodeSpaceCode target) := by
  unfold spaceCodeAdvance
  split
  · simp_all
  · rename_i next step
    split_ifs with head
    · constructor
      · intro same
        have codes := Option.some.inj same
        have decoded := congrArg M.decodeSpaceCode codes
        rw [DecisionView.decode_encode] at decoded
        simpa only [decoded] using step
      · intro same
        have views := Option.some.inj (step.symm.trans same)
        subst next
        rw [M.encode_decodeSpaceCode]
    · constructor
      · intro impossible
        cases impossible
      · intro same
        have views := Option.some.inj (step.symm.trans same)
        subst next
        exact False.elim (head (M.decodeSpaceCode_bounded data s target).workHead)

/-- The finite encoding and bounded views describe exactly the same vertices. -/
def spaceCodeEquiv (data : InputData I A) (s : ℕ) :
    M.SpaceCode data s ≃ M.BoundedDecisionView data s where
  toFun code := ⟨M.decodeSpaceCode code, M.decodeSpaceCode_bounded data s code⟩
  invFun view := view.val.encode M view.property
  left_inv := M.encode_decodeSpaceCode data s
  right_inv view := Subtype.ext (view.val.decode_encode M view.property)

def SpaceCodeEdge (data : InputData I A) (s : ℕ) (source target : M.SpaceCode data s) : Prop :=
  ∃ choice : Bool, M.spaceCodeAdvance data s choice source = some target

instance spaceCodeEdge_decidable (data : InputData I A) (s : ℕ) :
    DecidableRel (M.SpaceCodeEdge data s) := fun source target =>
  inferInstanceAs (Decidable (∃ choice : Bool, M.spaceCodeAdvance data s choice source = some target))

theorem spaceCodeEdge_iff (data : InputData I A) (s : ℕ) (source target : M.SpaceCode data s) :
    M.SpaceCodeEdge data s source target ↔
      M.BoundedDecisionEdge data s (M.spaceCodeEquiv data s source) (M.spaceCodeEquiv data s target) := by
  simp only [SpaceCodeEdge, spaceCodeAdvance_eq_some, BoundedDecisionEdge, DecisionEdge,
    spaceCodeEquiv, Equiv.coe_fn_mk]

theorem spaceCodePath_iff (data : InputData I A) (s : ℕ) (source target : M.SpaceCode data s) :
    Relation.ReflTransGen (M.SpaceCodeEdge data s) source target ↔
      Relation.ReflTransGen (M.BoundedDecisionEdge data s)
        (M.spaceCodeEquiv data s source) (M.spaceCodeEquiv data s target) := by
  constructor
  · intro path
    exact path.lift (M.spaceCodeEquiv data s) (fun a b edge => (M.spaceCodeEdge_iff data s a b).mp edge)
  · intro path
    have lifted := path.lift (M.spaceCodeEquiv data s).symm (fun a b edge =>
      (M.spaceCodeEdge_iff data s _ _).mpr (by simpa using edge))
    simpa only [Function.onFun, Equiv.symm_apply_apply] using lifted

def initialSpaceCode (data : InputData I A) (s : ℕ) : M.SpaceCode data s :=
  (M.spaceCodeEquiv data s).symm (M.boundedInitialView data s)

/-- Checking a halting instruction requires no equality test on output symbols. -/
def spaceCodeAccepting (data : InputData I A) (s : ℕ) (code : M.SpaceCode data s) : Bool :=
  let view := M.decodeSpaceCode code
  match M.transition view.state data.input[view.inputHead]? data.auxiliary[view.auxiliaryHead]?
      (if view.indexHead < data.index then some () else none) (view.work view.workHead) with
  | .accept => true
  | _ => false

theorem spaceCodeAccepting_iff (data : InputData I A) (s : ℕ) (code : M.SpaceCode data s) :
    M.spaceCodeAccepting data s code = true ↔ (M.decodeSpaceCode code).Accepting M data := by
  dsimp only [spaceCodeAccepting, DecisionView.Accepting]
  cases M.transition (M.decodeSpaceCode code).state
    data.input[(M.decodeSpaceCode code).inputHead]? data.auxiliary[(M.decodeSpaceCode code).auxiliaryHead]?
    (if (M.decodeSpaceCode code).indexHead < data.index then some () else none)
    ((M.decodeSpaceCode code).work (M.decodeSpaceCode code).workHead) <;> simp

theorem spaceCode_acceptance_iff (data : InputData I A) (s : ℕ) :
    (∃ finish : M.SpaceCode data s,
      Relation.ReflTransGen (M.SpaceCodeEdge data s) (M.initialSpaceCode data s) finish ∧
      M.spaceCodeAccepting data s finish = true) ↔
    ∃ finish : M.BoundedDecisionView data s,
      Relation.ReflTransGen (M.BoundedDecisionEdge data s) (M.boundedInitialView data s) finish ∧
      finish.val.Accepting M data := by
  simp only [spaceCodePath_iff, initialSpaceCode, Equiv.apply_symm_apply, spaceCodeAccepting_iff]
  constructor
  · rintro ⟨finish, path, accepting⟩
    exact ⟨M.spaceCodeEquiv data s finish, path, accepting⟩
  · rintro ⟨finish, path, accepting⟩
    refine ⟨(M.spaceCodeEquiv data s).symm finish, by simpa using path, ?_⟩
    exact (finish.val.decode_encode M finish.property) ▸ accepting

end ComplexityOfGenerators.Machine
