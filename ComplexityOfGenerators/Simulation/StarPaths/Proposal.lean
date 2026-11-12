import ComplexityOfGenerators.Simulation.StarPaths.Correctness

namespace ComplexityOfGenerators.Simulation.StarPaths
set_option backward.isDefEq.respectTransparency false

/-- Each cut coin closes the current factor. Factors are accumulated in
reverse order, which has no effect on their sum or availability. -/
def cutWalk : ℕ → List Bool → ℕ → Parts → Parts
  | 0, _, current, prior => current::prior
  | n+1, bits, current, prior =>
      if (bits[0]?).getD false then cutWalk n bits.tail 1 (current::prior)
      else cutWalk n bits.tail (current+1) prior

def proposal (n : ℕ) (bits : List Bool) : Parts :=
  if n = 0 then [] else cutWalk (n-1) bits 1 []

private theorem cutWalk_sum (n : ℕ) (bits : List Bool) (current : ℕ) (prior : Parts) :
    (cutWalk n bits current prior).sum = current+n+prior.sum := by
  induction n generalizing bits current prior with
  | zero => simp [cutWalk]
  | succ n ih =>
      simp only [cutWalk]
      split_ifs <;> rw [ih] <;> (try simp only [List.sum_cons]) <;> omega

private theorem cutWalk_positive (n : ℕ) (bits : List Bool) (current : ℕ) (prior : Parts)
    (positive : 0 < current) (valid : ∀ j ∈ prior, 0 < j) :
    ∀ j ∈ cutWalk n bits current prior, 0 < j := by
  induction n generalizing bits current prior with
  | zero =>
      intro j member
      rcases List.mem_cons.mp member with rfl | member
      · exact positive
      · exact valid j member
  | succ n ih =>
      simp only [cutWalk]
      split_ifs
      · apply ih _ 1 _ (by decide)
        intro j member
        rcases List.mem_cons.mp member with rfl | member
        · exact positive
        · exact valid j member
      · exact ih _ _ _ (by omega) valid

theorem proposal_sum (n : ℕ) (bits : List Bool) : (proposal n bits).sum = n := by
  unfold proposal
  split_ifs with zero
  · simp [zero]
  · rw [cutWalk_sum]
    simp only [List.sum_nil,Nat.add_zero]
    omega

theorem proposal_positive (n : ℕ) (bits : List Bool) : ∀ j ∈ proposal n bits, 0 < j := by
  unfold proposal
  split_ifs
  · simp
  · exact cutWalk_positive _ _ _ _ (by decide) (by simp)

private theorem cutWalk_false (count remaining : ℕ) (bits : List Bool) (current : ℕ) (prior : Parts) :
    cutWalk (count+remaining) (List.replicate count false++bits) current prior =
      cutWalk remaining bits (current+count) prior := by
  induction count generalizing current with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ,List.cons_append,Nat.succ_add,cutWalk,List.getElem?_cons_zero,
        Option.getD_some,Bool.false_eq_true,ite_false,List.tail_cons]
      rw [ih]
      congr 1
      omega

/-- Exactly one coin between successive unary units is sufficient. -/
def cutCoins : Parts → List Bool
  | [] => []
  | j::rest => List.replicate (j-1) false ++ if rest = [] then [] else true::cutCoins rest

private theorem cutCoins_length (parts : Parts) (positive : ∀ j ∈ parts, 0 < j) :
    (cutCoins parts).length = parts.sum-1 := by
  induction parts with
  | nil => rfl
  | cons j rest ih =>
      have first := positive j (by simp)
      have tail : ∀ k ∈ rest, 0 < k := fun k member => positive k (by simp [member])
      have restPositive : rest ≠ [] → 0 < rest.sum := by
        intro nonempty
        cases rest with
        | nil => contradiction
        | cons k more => have := tail k (by simp); simp only [List.sum_cons]; omega
      simp only [cutCoins,List.length_append,List.length_replicate,List.sum_cons]
      split_ifs with empty
      · subst rest; simp <;> omega
      · simp only [List.length_cons,ih tail]
        have := restPositive empty
        omega

private theorem cutWalk_coins (parts : Parts) (nonempty : parts ≠ [])
    (positive : ∀ j ∈ parts, 0 < j) (prior : Parts) :
    cutWalk (parts.sum-1) (cutCoins parts) 1 prior = parts.reverse++prior := by
  induction parts generalizing prior with
  | nil => contradiction
  | cons j rest ih =>
      have first := positive j (by simp)
      have tail : ∀ k ∈ rest, 0 < k := fun k member => positive k (by simp [member])
      by_cases empty : rest = []
      · subst rest
        simp only [cutCoins,ite_true,List.append_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
        have walked := cutWalk_false (j-1) 0 [] 1 prior
        simp only [Nat.add_zero,List.append_nil,cutWalk] at walked
        rw [walked]
        simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append]
        have index : 1+(j-1) = j := by omega
        rw [index]
      · have restPositive : 0 < rest.sum := by
          cases rest with
          | nil => contradiction
          | cons k more => have := tail k (by simp); simp only [List.sum_cons]; omega
        have length : (j::rest).sum-1 = (j-1)+(rest.sum-1+1) := by simp only [List.sum_cons]; omega
        rw [length]
        simp only [cutCoins,if_neg empty]
        rw [cutWalk_false]
        have index : 1+(j-1) = j := by omega
        rw [index]
        simp only [cutWalk,List.getElem?_cons_zero,Option.getD_some,ite_true,List.tail_cons]
        rw [ih empty tail]
        simp [List.reverse_cons,List.append_assoc]

/-- Every positive composition of n is represented by a fixed block of n-1
cut coins. No rejection or random search over decompositions is needed. -/
theorem proposal_full_support (n : ℕ) (parts : Parts) (total : parts.sum = n)
    (positive : ∀ j ∈ parts, 0 < j) :
    ∃ bits : List Bool, bits.length = n-1 ∧ proposal n bits = parts := by
  by_cases zero : n = 0
  · have empty : parts = [] := by
      cases parts with
      | nil => rfl
      | cons j rest => have := positive j (by simp); simp only [List.sum_cons] at total; omega
    subst parts
    exact ⟨[],by simp [zero],by simp [proposal,zero]⟩
  · have nonempty : parts.reverse ≠ [] := by
      intro empty
      have original : parts = [] := List.reverse_eq_nil_iff.mp empty
      simp [original] at total
      omega
    refine ⟨cutCoins parts.reverse,?_,?_⟩
    · rw [cutCoins_length _ (by simpa using positive),List.sum_reverse,total]
    · unfold proposal
      rw [if_neg zero,← total,← List.sum_reverse (xs := parts)]
      have selected := cutWalk_coins parts.reverse nonempty (by simpa using positive) []
      simpa using selected

end ComplexityOfGenerators.Simulation.StarPaths
