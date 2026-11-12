import ComplexityOfGenerators.Examples.SATNative.HeaderStep

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader

theorem step_invalid (state : ScanState) (invalid : state.valid = false) : (step state).valid = false := by
  cases word : state.word with
  | nil => simp [step, word]
  | cons head rest => cases head <;> simp [step, word, invalid]

theorem iterate_invalid (state : ScanState) (invalid : state.valid = false) (count : ℕ) :
    (step^[count] state).valid = false := by
  induction count generalizing state with
  | zero => exact invalid
  | succ count ih => rw [Function.iterate_succ_apply]; exact ih (step state) (step_invalid state invalid)

theorem bad_first (state : ScanState) (invalid : (step state).valid = false) (count : ℕ) :
    (step^[count + 1] state).valid = false := by
  rw [Function.iterate_succ_apply]
  exact iterate_invalid (step state) invalid count

def restrict (state : ScanState) (enabled : Bool) : ScanState :=
  {state with valid := state.valid && enabled}

theorem step_restrict (state : ScanState) (enabled : Bool) :
    step (restrict state enabled) = restrict (step state) enabled := by
  obtain ⟨word, count, ones, valid⟩ := state
  cases word with
  | nil => rfl
  | cons head rest => cases head <;>
      simp [step, restrict, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem iterate_restrict (count : ℕ) (state : ScanState) (enabled : Bool) :
    step^[count] (restrict state enabled) = restrict (step^[count] state) enabled := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, step_restrict, ih, Function.iterate_succ_apply]

theorem iterate_ones (count initial : ℕ) (rest : List Symbol) (valid : Bool) :
    step^[count] ⟨List.replicate count .one ++ rest, initial, true, valid⟩ =
      ⟨rest, initial + count, true, valid⟩ := by
  induction count generalizing initial with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, Function.iterate_succ_apply, step,
      ite_true, Bool.and_true]
    rw [ih]
    congr 1
    omega

theorem iterate_zeros (count initial : ℕ) (rest : List Symbol) (ones valid : Bool) :
    step^[count] ⟨List.replicate count .zero ++ rest, initial, ones, valid⟩ =
      ⟨rest, initial, if count = 0 then ones else false, valid⟩ := by
  induction count generalizing ones with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, Function.iterate_succ_apply, step]
    rw [ih]
    simp

theorem iterate_canonical (ones zeros : ℕ) (rest : List Symbol) :
    step^[zeros + ones] ⟨List.replicate ones .one ++ List.replicate zeros .zero ++ rest, 0, true, true⟩ =
      ⟨rest, ones, decide (zeros = 0), true⟩ := by
  rw [Function.iterate_add_apply]
  have first := iterate_ones ones 0 (List.replicate zeros .zero ++ rest) true
  rw [← List.append_assoc] at first
  rw [first, iterate_zeros]
  by_cases zero : zeros = 0 <;> simp [zero]

/-- Every successful active-count scan consumed exactly a canonical unary
ones-then-zeros field. This is soundness on arbitrary input words. -/
theorem iterate_sound (count : ℕ) (word : List Symbol) (initial : ℕ) (ones : Bool)
    (accepted : (step^[count] ⟨word, initial, ones, true⟩).valid = true) :
    ∃ active ≤ count, (ones = false → active = 0) ∧
      word = List.replicate active .one ++ List.replicate (count - active) .zero ++
        (step^[count] ⟨word, initial, ones, true⟩).word ∧
      (step^[count] ⟨word, initial, ones, true⟩).count = initial + active := by
  induction count generalizing word initial ones with
  | zero => exact ⟨0, le_rfl, fun _ => rfl, by simp, by simp⟩
  | succ count ih =>
    cases word with
    | nil =>
      have bad := bad_first ⟨[], initial, ones, true⟩ rfl count
      rw [bad] at accepted
      cases accepted
    | cons head rest =>
      by_cases unary : head = .one
      · subst head
        cases ones with
        | false =>
          have bad := bad_first ⟨.one :: rest, initial, false, true⟩ rfl count
          rw [bad] at accepted
          cases accepted
        | true =>
          rw [Function.iterate_succ_apply] at accepted
          change (step^[count] ⟨rest, initial + 1, true, true⟩).valid = true at accepted
          obtain ⟨active, bound, _, equal, number⟩ := ih rest (initial + 1) true accepted
          refine ⟨active + 1, by omega, by simp, ?_, ?_⟩
          · change .one :: rest = List.replicate (active + 1) .one ++
              List.replicate (count + 1 - (active + 1)) .zero ++
                (step^[count] ⟨rest, initial + 1, true, true⟩).word
            conv_lhs => rw [equal]
            simp [List.replicate_succ, Nat.add_sub_add_right, List.append_assoc]
          · change (step^[count] ⟨rest, initial + 1, true, true⟩).count = initial + (active + 1)
            omega
      · by_cases zero : head = .zero
        · subst head
          rw [Function.iterate_succ_apply] at accepted
          change (step^[count] ⟨rest, initial, false, true⟩).valid = true at accepted
          obtain ⟨active, _, noOnes, equal, number⟩ := ih rest initial false accepted
          have activeZero := noOnes rfl
          subst active
          refine ⟨0, Nat.zero_le _, fun _ => rfl, ?_, ?_⟩
          · change .zero :: rest = List.replicate 0 .one ++ List.replicate (count + 1 - 0) .zero ++
                (step^[count] ⟨rest, initial, false, true⟩).word
            conv_lhs => rw [equal]
            simp [List.replicate_succ]
          · exact number
        · have invalid : (step ⟨head :: rest, initial, ones, true⟩).valid = false := by
            cases head <;> simp_all [step]
          have bad := bad_first ⟨head :: rest, initial, ones, true⟩ invalid count
          rw [bad] at accepted
          cases accepted

end ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader
