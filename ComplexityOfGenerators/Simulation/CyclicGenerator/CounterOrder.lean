import ComplexityOfGenerators.Simulation.CyclicGenerator.Counter

/-! The counter visits words in their finite base-alphabet order. The rank is
used only in the proof of enumeration, never stored in the machine's control. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section

variable {α : Type} [Fintype α]

def wordRank : List α → ℕ
  | [] => 0
  | a :: tail => (alphabet a).val + Fintype.card α * wordRank tail

theorem wordRank_lt (word : List α) : wordRank word < Fintype.card α ^ word.length := by
  induction word with
  | nil => simp [wordRank]
  | cons a tail ih =>
      have letter := (alphabet a).isLt
      simp only [wordRank, List.length_cons, pow_succ]
      nlinarith

theorem firstLetter_rank (a : α) (first : firstLetter = some a) : (alphabet a).val = 0 := by
  unfold firstLetter at first
  split at first
  · cases first
    simp
  · cases first

theorem nextLetter_rank (a b : α) (next : nextLetter a = some b) :
    (alphabet b).val = (alphabet a).val + 1 := by
  unfold nextLetter at next
  split at next
  · cases next
    simp
  · cases next

theorem nextLetter_last (a : α) (last : nextLetter a = none) :
    (alphabet a).val + 1 = Fintype.card α := by
  unfold nextLetter at last
  split at last
  · cases last
  · have letter := (alphabet a).isLt
    omega

theorem wordRank_replicate (a : α) (first : firstLetter = some a) (n : ℕ) :
    wordRank (List.replicate n a) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, wordRank, firstLetter_rank a first, ih]

/-- Every non-overflowing increment advances the rank by exactly one. At
overflow it resets all letters and the previous word had the largest rank. -/
theorem incrementWord_rank (first : α) (least : firstLetter = some first) (word : List α) :
    if (incrementWord first word).overflow then
      wordRank word + 1 = Fintype.card α ^ word.length ∧
        (incrementWord first word).word = List.replicate word.length first ∧
        (incrementWord first word).position = word.length
    else wordRank (incrementWord first word).word = wordRank word + 1 := by
  induction word with
  | nil => simp [incrementWord, wordRank]
  | cons a tail ih =>
      cases next : nextLetter a with
      | some b =>
          simp [incrementWord, next, wordRank, nextLetter_rank a b next, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
      | none =>
          have last := nextLetter_last a next
          have zero := firstLetter_rank first least
          cases overflow : (incrementWord first tail).overflow <;>
            simp only [overflow, Bool.false_eq_true, if_false, if_true] at ih
          · simp only [incrementWord, next, overflow, Bool.false_eq_true, if_false, wordRank, zero,
              zero_add]
            rw [ih]
            nlinarith
          · simp only [incrementWord, next, overflow, if_true, List.length_cons, wordRank,
              List.replicate_succ, List.cons.injEq, true_and]
            refine ⟨?_, ih.2.1, ih.2.2 ▸ rfl⟩
            rw [pow_succ]
            nlinarith [ih.1]

theorem wordRank_injective_of_length {left right : List α} (length : left.length = right.length)
    (rank : wordRank left = wordRank right) : left = right := by
  induction left generalizing right with
  | nil => simpa using length.symm
  | cons a tail ih =>
      cases right with
      | nil => simp at length
      | cons b rest =>
          have aBound := (alphabet a).isLt
          have bBound := (alphabet b).isLt
          have modulus := congrArg (fun n => n % Fintype.card α) rank
          simp only [wordRank, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt aBound,
            Nat.mod_eq_of_lt bBound] at modulus
          have letters : a = b := alphabet.injective (Fin.ext modulus)
          subst b
          have tails : wordRank tail = wordRank rest := by
            simp only [wordRank, Nat.add_left_cancel_iff] at rank
            exact Nat.eq_of_mul_eq_mul_left (by omega) rank
          exact congrArg (List.cons a) (ih (by simpa using length) tails)

theorem incrementWord_before (first : α) (least : firstLetter = some first)
    (word target : List α) (length : word.length = target.length)
    (before : wordRank word < wordRank target) :
    (incrementWord first word).overflow = false ∧
      wordRank (incrementWord first word).word = wordRank word + 1 := by
  have rank := incrementWord_rank first least word
  cases overflow : (incrementWord first word).overflow with
  | false => exact ⟨rfl, by simpa [overflow] using rank⟩
  | true =>
      simp only [overflow, ite_true] at rank
      have last := rank.1
      have bound := wordRank_lt target
      rw [← length] at bound
      omega

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
