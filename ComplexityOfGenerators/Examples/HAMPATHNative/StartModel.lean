import ComplexityOfGenerators.Examples.HAMPATHNative.Start

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

theorem startStep_invalid (state : StartState) (invalid : state.valid = false) :
    (startStep state).valid = false := by
  cases word : state.word with
  | nil => simp [startStep, word]
  | cons head rest => cases head with
    | separator => simp [startStep, word]
    | bit value => cases value <;> simp [startStep, word, invalid]

theorem startIterate_invalid (state : StartState) (invalid : state.valid = false) (count : ℕ) :
    (startStep^[count] state).valid = false := by
  induction count generalizing state with
  | zero => exact invalid
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      exact ih (startStep state) (startStep_invalid state invalid)

theorem startIterate_initialValid (state : StartState) (count : ℕ)
    (accepted : (startStep^[count] state).valid = true) : state.valid = true := by
  cases valid : state.valid with
  | true => rfl
  | false => rw [startIterate_invalid state valid count] at accepted; cases accepted

theorem startIterate_seenSound (count : ℕ) (word : List Symbol) (initial : ℕ)
    (accepted : (startStep^[count] ⟨word, initial, true, true⟩).valid = true) :
    word = List.replicate count (.bit false) ++ (startStep^[count] ⟨word, initial, true, true⟩).word ∧
      (startStep^[count] ⟨word, initial, true, true⟩).start = initial ∧
      (startStep^[count] ⟨word, initial, true, true⟩).seen = true := by
  induction count generalizing word with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply] at accepted ⊢
      have first := startIterate_initialValid (startStep ⟨word, initial, true, true⟩) count accepted
      cases word with
      | nil => simp [startStep] at first
      | cons head rest => cases head with
        | separator => simp [startStep] at first
        | bit value => cases value with
          | true => simp [startStep] at first
          | false =>
              change (startStep^[count] ⟨rest, initial, true, true⟩).valid = true at accepted
              obtain ⟨reconstruct, number, seen⟩ := ih rest accepted
              refine ⟨?_, number, seen⟩
              simpa only [startStep, ite_true, List.replicate_succ, List.cons_append]
                using congrArg (Symbol.bit false :: ·) reconstruct

/-- A successful start field contains exactly one marked vertex. Its unary
counter records that vertex, including on arbitrary malformed source words. -/
theorem startIterate_sound (count : ℕ) (word : List Symbol) (initial : ℕ)
    (accepted : (startStep^[count] ⟨word, initial, false, true⟩).valid = true)
    (seen : (startStep^[count] ⟨word, initial, false, true⟩).seen = true) :
    ∃ start < count,
      word = List.replicate start (.bit false) ++ .bit true ::
        (List.replicate (count - start - 1) (.bit false) ++
          (startStep^[count] ⟨word, initial, false, true⟩).word) ∧
      (startStep^[count] ⟨word, initial, false, true⟩).start = initial + start := by
  induction count generalizing word initial with
  | zero => simp at seen
  | succ count ih =>
      rw [Function.iterate_succ_apply] at accepted seen ⊢
      have first := startIterate_initialValid (startStep ⟨word, initial, false, true⟩) count accepted
      cases word with
      | nil => simp [startStep] at first
      | cons head rest => cases head with
        | separator => simp [startStep] at first
        | bit value => cases value with
          | false =>
              change (startStep^[count] ⟨rest, initial + 1, false, true⟩).valid = true at accepted
              change (startStep^[count] ⟨rest, initial + 1, false, true⟩).seen = true at seen
              obtain ⟨start, bound, reconstruct, number⟩ := ih rest (initial + 1) accepted seen
              refine ⟨start + 1, by omega, ?_, ?_⟩
              · change .bit false :: rest = List.replicate (start + 1) (.bit false) ++ .bit true ::
                  (List.replicate (count + 1 - (start + 1) - 1) (.bit false) ++ _)
                simpa only [startStep, Bool.false_eq_true, ite_false, List.replicate_succ,
                  List.cons_append, Nat.add_sub_add_right] using congrArg (Symbol.bit false :: ·) reconstruct
              · change (startStep^[count] ⟨rest, initial + 1, false, true⟩).start = initial + (start + 1)
                omega
          | true =>
              change (startStep^[count] ⟨rest, initial, true, true⟩).valid = true at accepted
              obtain ⟨reconstruct, number, _⟩ := startIterate_seenSound count rest initial accepted
              refine ⟨0, by omega, ?_, ?_⟩
              · simpa only [startStep, Bool.not_false, Bool.and_true, Nat.sub_zero, Nat.add_sub_cancel,
                  List.replicate_zero, List.nil_append] using congrArg (Symbol.bit true :: ·) reconstruct
              · simpa [startStep] using number

theorem startIterate_zeros (count initial : ℕ) (tail : List Symbol) (seen valid : Bool) :
    startStep^[count] ⟨List.replicate count (.bit false) ++ tail, initial, seen, valid⟩ =
      ⟨tail, if seen then initial else initial + count, seen, valid⟩ := by
  induction count generalizing initial with
  | zero => cases seen <;> simp
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, Function.iterate_succ_apply, startStep]
      rw [ih]
      cases seen <;> simp
      omega

def oneHot (size start : ℕ) : List Symbol :=
  List.replicate start (.bit false) ++ .bit true :: List.replicate (size - start - 1) (.bit false)

theorem startIterate_complete (size start : ℕ) (inside : start < size) (tail : List Symbol) :
    startStep^[size] ⟨oneHot size start ++ tail, 0, false, true⟩ = ⟨tail, start, true, true⟩ := by
  have count : size = (size - start - 1) + 1 + start := by omega
  rw [show startStep^[size] = startStep^[(size - start - 1) + 1 + start] from
    congrArg (fun n => startStep^[n]) count, Function.iterate_add_apply]
  have first := startIterate_zeros start 0
    (.bit true :: (List.replicate (size - start - 1) (.bit false) ++ tail)) false true
  simp only [oneHot, List.append_assoc, List.cons_append]
  change startStep^[(size - start - 1) + 1]
    (startStep^[start] ⟨List.replicate start (.bit false) ++
      (.bit true :: (List.replicate (size - start - 1) (.bit false) ++ tail)), 0, false, true⟩) = _
  rw [first]
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add, Function.iterate_succ_apply, startStep,
    Bool.not_false, Bool.and_true]
  rw [startIterate_zeros]
  rfl

end ComplexityOfGenerators.Examples.HAMPATH.Native
