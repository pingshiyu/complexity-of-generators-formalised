import ComplexityOfGenerators.Examples.HAMPATHNative.ParserBounds
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem startStep_word (state : StartState) : (startStep state).word = state.word.tail := by
  cases word : state.word with
  | nil => simp [startStep, word]
  | cons head rest => cases head with
    | separator => simp [startStep, word]
    | bit value => cases value <;> simp [startStep, word]

theorem startStep_start (state : StartState) : (startStep state).start ≤ state.start + 1 := by
  cases word : state.word with
  | nil => simp [startStep, word]
  | cons head rest => cases head with
    | separator => simp [startStep, word]
    | bit value => cases value <;> simp [startStep, word]; split <;> omega

theorem startIterate_start (state : StartState) (count : ℕ) :
    (startStep^[count] state).start ≤ state.start + count := by
  induction count generalizing state with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      have next := ih (startStep state)
      have first := startStep_start state
      omega

theorem startIterate_word (state : StartState) (count : ℕ) :
    (startStep^[count] state).word = state.word.drop count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, ih, startStep_word, List.drop_tail]

theorem separator_row (state : RowState) : (separator state).row = state.row := by
  unfold separator
  split <;> rfl

theorem separator_word_le (state : RowState) : (separator state).word.length ≤ state.word.length := by
  unfold separator
  split <;> simp [List.length_tail]

theorem afterMatrix_row (word : List Symbol) : (afterMatrix word).row = headerSize word := by
  rw [afterMatrix, separator_row, matrixState, rowIterate_number, headerState_row, Nat.zero_add]

theorem afterMatrix_word_le (word : List Symbol) : (afterMatrix word).word.length ≤ word.length := by
  exact (separator_word_le (matrixState word)).trans
    ((rowIterate_word_le (headerSize word) (headerSize word) (headerState word)).trans (headerState_word_le word))

theorem parsedState_bounds (word : List Symbol) :
    (parsedState word).start ≤ headerSize word ∧ (parsedState word).word.length ≤ word.length := by
  constructor
  · simpa only [parsedState, Nat.zero_add] using
      startIterate_start ⟨(afterMatrix word).word, 0, false, (afterMatrix word).valid⟩ (headerSize word)
  · change (startStep^[headerSize word] _).word.length ≤ word.length
    rw [startIterate_word]
    exact (by simp : ((afterMatrix word).word.drop (headerSize word)).length ≤ (afterMatrix word).word.length).trans
      (afterMatrix_word_le word)

theorem header_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((header (O := O)).eval s) (budget + 1) := by
  have source := sizes 2
  have sizeBound := headerSize_le (s 2)
  have wordBound := headerState_word_le (s 2)
  intro j
  rw [header_eval]
  fin_cases j <;> simp [rowEncoded, cellEncoded, headerBase, flag, headerState_row] <;>
    (try split) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact (sizes _).trans (by omega) | omega

theorem parser_bound {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((parser (O := O)).eval s j).length ≤ budget + 1 := by
  have source := sizes 2
  have sizeBound := headerSize_le (s 2)
  have startBound := (parsedState_bounds (s 2)).1
  have wordBound := (parsedState_bounds (s 2)).2
  intro j
  rw [parser_eval]
  fin_cases j <;> simp [startEncoded, rowEncoded, cellEncoded, headerBase, flag, afterMatrix_row] <;>
    (try split) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact (sizes _).trans (by omega) | omega

end ComplexityOfGenerators.Examples.HAMPATH.Native
