import ComplexityOfGenerators.Simulation.CyclicGenerator.CounterOrder

/-! A word counter with growing length. Its first polynomially many values
cover all labels of logarithmic length; no runtime logarithm is required. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Shortlex

noncomputable section

open CyclicGenerator
variable {α : Type} [Fintype α]

def next (first : α) : List α → List α
  | [] => [first]
  | a :: tail => match nextLetter a with
    | some b => b :: tail
    | none => first :: next first tail

theorem next_eq (first : α) (word : List α) :
    next first word = if (incrementWord first word).overflow then
      (incrementWord first word).word ++ [first] else (incrementWord first word).word := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
    cases letter : nextLetter a with
    | some b => simp [next, incrementWord, letter]
    | none =>
      cases overflow : (incrementWord first tail).overflow <;>
        simp [next, incrementWord, letter, ih, overflow]

def offset (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => offset a n + a ^ n

theorem offset_mono (a : ℕ) : Monotone (offset a) := by
  apply monotone_nat_of_le_succ
  intro n
  simp [offset]

def rank (word : List α) : ℕ := offset (Fintype.card α) word.length + wordRank word

theorem rank_lt (word : List α) : rank word < offset (Fintype.card α) (word.length + 1) := by
  have := wordRank_lt word
  simp only [rank, offset]
  omega

theorem rank_injective : Function.Injective (rank (α := α)) := by
  intro left right equal
  have length : left.length = right.length := by
    by_contra different
    rcases lt_or_gt_of_ne different with less | less
    · have h₁ := rank_lt left
      have h₂ := offset_mono (Fintype.card α) (show left.length + 1 ≤ right.length by omega)
      have h₃ : offset (Fintype.card α) right.length ≤ rank right := Nat.le_add_right ..
      omega
    · have h₁ := rank_lt right
      have h₂ := offset_mono (Fintype.card α) (show right.length + 1 ≤ left.length by omega)
      have h₃ : offset (Fintype.card α) left.length ≤ rank left := Nat.le_add_right ..
      omega
  apply wordRank_injective_of_length length
  unfold rank at equal
  rw [length] at equal
  omega

theorem next_rank (first : α) (least : firstLetter = some first) (word : List α) :
    rank (next first word) = rank word + 1 := by
  rw [next_eq]
  have order := incrementWord_rank first least word
  cases overflow : (incrementWord first word).overflow with
  | false =>
    simp only [overflow, Bool.false_eq_true, ite_false] at *
    simp only [rank, incrementWord_length, order]
    omega
  | true =>
    simp only [overflow, ite_true] at *
    rw [order.2.1]
    have replicated : List.replicate word.length first ++ [first] = List.replicate (word.length + 1) first := by
      rw [List.replicate_add]; rfl
    rw [replicated]
    simp only [rank, List.length_replicate, wordRank_replicate first least, Nat.add_zero, offset]
    omega

theorem iterate_rank (first : α) (least : firstLetter = some first) (n : ℕ) :
    rank ((next first)^[n] []) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', next_rank first least, ih]

theorem reaches (first : α) (least : firstLetter = some first) (word : List α) :
    (next first)^[rank word] [] = word := rank_injective (iterate_rank first least _)

theorem next_length (first : α) (word : List α) : (next first word).length ≤ word.length + 1 := by
  rw [next_eq]
  split <;> simp [incrementWord_length]

theorem iterate_length (first : α) (n : ℕ) : ((next first)^[n] []).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (next_length first _).trans (by omega)

theorem offset_bound (a n : ℕ) (positive : 0 < a) : offset a n ≤ (a + 1) ^ n := by
  induction n with
  | zero => simp [offset]
  | succ n ih =>
    have power : a ^ n ≤ (a + 1) ^ n := pow_le_pow_left' (by omega) n
    simp only [offset, pow_succ]
    nlinarith

theorem rank_bound (word : List α) (positive : 0 < Fintype.card α) :
    rank word < (Fintype.card α + 1) ^ (word.length + 1) :=
  (rank_lt word).trans_le (offset_bound _ _ positive)

def labels (first : α) (count : ℕ) : List (List α) := (List.range count).map (fun i => (next first)^[i] [])

@[simp] theorem labels_length (first : α) (count : ℕ) : (labels first count).length = count := by simp [labels]

theorem mem_labels (first : α) (least : firstLetter = some first) (word : List α) (count : ℕ)
    (bounded : rank word < count) : word ∈ labels first count := by
  exact List.mem_map.mpr ⟨rank word, List.mem_range.mpr bounded, reaches first least word⟩

end
end ComplexityOfGenerators.Simulation.WordStack.Shortlex
