import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

variable {α Q S : Type} {k : ℕ} (B : TapeBank α Bool Unit Q S k)

/-- The immutable guessed word occupies exactly the nonnegative finite prefix;
its source-work component stays blank. -/
def wordTape (word : Word α) (position : ℤ) : Cell S α :=
  (B.blank, if 0 ≤ position then word[position.toNat]? else none)

@[simp] theorem wordTape_source (word : Word α) (position : ℤ) :
    (wordTape B word position).1 = B.blank := rfl

@[simp] theorem wordTape_read (word : Word α) (position : ℕ) :
    (wordTape B word position).2 = word[position]? := by simp [wordTape]

@[simp] theorem wordTape_nil : wordTape B [] = fun _ => (B.blank, none) := by
  funext p
  simp [wordTape]

/-- Appending a guessed letter is one real cell write at the current right end. -/
theorem wordTape_append (word : Word α) (value : α) :
    Function.update (wordTape B word) (word.length : ℤ) (B.blank, some value) =
      wordTape B (word ++ [value]) := by
  funext p
  cases p with
  | ofNat position =>
    by_cases before : position < word.length
    · have different : (position : ℤ) ≠ word.length := by omega
      simp [Function.update_of_ne different, wordTape, List.getElem?_append_left before]
    · by_cases ended : position = word.length
      · subst position
        simp [wordTape]
      · have after : word.length < position := by omega
        have noOld : word[position]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have noNew : (word ++ [value])[position]? = none :=
          List.getElem?_eq_none_iff.mpr (by simp; omega)
        have different : (position : ℤ) ≠ word.length := by omega
        simp [Function.update_of_ne different, wordTape, noOld, noNew]
  | negSucc position =>
    have different : Int.negSucc position ≠ (word.length : ℤ) := by omega
    simp [Function.update_of_ne different, wordTape]

theorem wordTape_isSome (word : Word α) (position : ℕ) :
    (wordTape B word position).2.isSome = decide (position < word.length) := by
  rw [wordTape_read]
  by_cases live : position < word.length
  · rw [List.getElem?_eq_getElem live]
    simp [live]
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]
    simp [live]

/-- Actual word-tape head moves implement the ordinary source input's boundary
clamping, without storing an input position in finite control. -/
theorem inputMove_position (word : Word α) (position : ℕ) (bounded : position ≤ word.length)
    (move : Move) :
    (inputMove move (decide ((position : ℤ) = 0)) (wordTape B word position).2).onInt position =
      (move.onInput word.length position : ℤ) := by
  cases move with
  | left =>
    by_cases zero : position = 0
    · subst position; simp [inputMove, Move.onInput, Move.onInt]
    · simp [inputMove, Move.onInput, zero, Move.onInt]; omega
  | stay => simp [inputMove, Move.onInput, Move.onInt]; omega
  | right =>
    by_cases live : position < word.length <;>
      simp [inputMove, wordTape_isSome, live, Move.onInput, Move.onInt] <;> omega

end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
