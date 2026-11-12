import ComplexityOfGenerators.Examples.SATNative.BodyLoopBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeParser

open NativeBody

/-- The finite-control parser's mathematical output. Every iteration is
implemented by `NativeBody.bodyStep`, not by the checked functional decoder. -/
def finalState (word : List Symbol) : NativeBody.State :=
  let header := NativeHeader.parsedState word
  (NativeBody.step (readOnes word).1 header.count)^[header.word.length]
    ⟨header.word, false, false, header.valid⟩

def accepted (word : List Symbol) : Bool := NativeBody.accepts (finalState word)

theorem body_iterate_invalid (capacity active count : ℕ) (state : NativeBody.State)
    (invalid : state.valid = false) :
    ((NativeBody.step capacity active)^[count] state).valid = false := by
  induction count generalizing state with
  | zero => exact invalid
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (NativeBody.step_invalid capacity active state invalid)

theorem accepted_sound (word : List Symbol) (success : accepted word = true) :
    ∃ (capacity active : ℕ) (formula : Formula), active ≤ capacity ∧ formula.valid active ∧
      formula.encode capacity active = word := by
  have headerValid : (NativeHeader.parsedState word).valid = true := by
    cases valid : (NativeHeader.parsedState word).valid with
    | true => rfl
    | false =>
      have bad := body_iterate_invalid (readOnes word).1 (NativeHeader.parsedState word).count
        (NativeHeader.parsedState word).word.length
        ⟨(NativeHeader.parsedState word).word, false, false, (NativeHeader.parsedState word).valid⟩ valid
      have impossible : (finalState word).valid = false := bad
      simp [accepted, NativeBody.accepts, impossible] at success
  obtain ⟨capacity, bound, reconstruct⟩ := NativeHeader.parsedState_sound word headerValid
  have capacityEq : (readOnes word).1 = capacity := by
    rw [reconstruct, readOnes_header]
  have bodySuccess : NativeBody.accepts
      ((NativeBody.step (readOnes word).1 (NativeHeader.parsedState word).count)^[(NativeHeader.parsedState word).word.length]
        (NativeBody.initial (NativeHeader.parsedState word).word)) = true := by
    simpa [accepted, finalState, NativeBody.initial, headerValid] using success
  obtain ⟨formula, valid, body⟩ := NativeBody.accepted_sound (readOnes word).1
    (NativeHeader.parsedState word).count (NativeHeader.parsedState word).word.length _ bodySuccess
  refine ⟨capacity, (NativeHeader.parsedState word).count, formula, bound, valid, ?_⟩
  have equalBody : formula.bodyWord capacity = (NativeHeader.parsedState word).word := by
    rw [← capacityEq]
    exact body.symm
  calc
    formula.encode capacity (NativeHeader.parsedState word).count = List.replicate capacity .one ++
      .separator :: (List.replicate (NativeHeader.parsedState word).count .one ++
        List.replicate (capacity - (NativeHeader.parsedState word).count) .zero ++
          .separator :: formula.bodyWord capacity) := by
      simp [Formula.encode, Formula.bodyWord, List.append_assoc]
    _ = word := by rw [equalBody]; exact reconstruct.symm

theorem header_encode (capacity active : ℕ) (bound : active ≤ capacity) (formula : Formula) :
    NativeHeader.parsedState (formula.encode capacity active) =
      ⟨formula.bodyWord capacity, active, decide (capacity - active = 0), true⟩ := by
  convert NativeHeader.parsedState_canonical capacity active bound (formula.bodyWord capacity) using 1 <;>
    simp [Formula.encode, Formula.bodyWord, List.append_assoc]

theorem capacity_encode (capacity active : ℕ) (formula : Formula) :
    (readOnes (formula.encode capacity active)).1 = capacity := by
  have shape : formula.encode capacity active = List.replicate capacity .one ++ .separator ::
      (List.replicate active .one ++ List.replicate (capacity - active) .zero ++
        .separator :: formula.bodyWord capacity) := by
    simp [Formula.encode, Formula.bodyWord, List.append_assoc]
  rw [shape, readOnes_header]

theorem accepted_encode {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) : accepted (formula.encode capacity active) = true := by
  unfold accepted finalState
  rw [header_encode capacity active bound, capacity_encode]
  exact NativeBody.accepted_encode bound formula valid _ (NativeBody.tokenCount_bound bound formula valid)

theorem accepted_iff (word : List Symbol) :
    accepted word = true ↔ (decode word).isSome = true := by
  constructor
  · intro success
    obtain ⟨capacity, active, formula, bound, valid, equal⟩ := accepted_sound word success
    rw [← equal, decode_encode bound formula valid]
    rfl
  · intro decoded
    obtain ⟨triple, result⟩ := Option.isSome_iff_exists.mp decoded
    rcases triple with ⟨capacity, active, formula⟩
    obtain ⟨bound, valid, equal⟩ := decode_sound word capacity active formula result
    rw [← equal]
    exact accepted_encode bound formula valid

theorem accepted_eq_decode (word : List Symbol) : accepted word = (decode word).isSome := by
  exact Bool.eq_iff_iff.mpr (accepted_iff word)

end ComplexityOfGenerators.Examples.PaddedCNF.NativeParser
