import ComplexityOfGenerators.Simulation.TransducerBank.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

 theorem Steps.random_monotone {data : InputData I A} {bits : BitString}
    {a b : BankConfiguration O Q S k} {t : ℕ} (path : B.Steps data bits a t b) :
    a.randomHead ≤ b.randomHead := by
  induction path with
  | refl => exact le_rfl
  | step a next write work input auxiliary index emit t b table rest ih => exact ih
  | random a no yes bit t b table lookup rest ih =>
      change a.randomHead + 1 ≤ b.randomHead at ih
      omega

theorem Steps.random_growth {data : InputData I A} {bits : BitString}
    {a b : BankConfiguration O Q S k} {t : ℕ} (path : B.Steps data bits a t b) :
    b.randomHead ≤ a.randomHead + t := by
  induction path with
  | refl => simp
  | step a next write work input auxiliary index emit t b table rest ih =>
      change b.randomHead ≤ a.randomHead + t at ih
      omega
  | random a no yes bit t b table lookup rest ih =>
      change b.randomHead ≤ a.randomHead + 1 + t at ih
      omega

theorem Steps.random_le_length {data : InputData I A} {bits : BitString}
    {a b : BankConfiguration O Q S k} {t : ℕ} (path : B.Steps data bits a t b)
    (bound : a.randomHead ≤ bits.length) : b.randomHead ≤ bits.length := by
  induction path with
  | refl => exact bound
  | step a next write work input auxiliary index emit t b table rest ih => exact ih bound
  | random a no yes bit t b table lookup rest ih =>
      apply ih
      have available := (List.getElem?_eq_some_iff.mp lookup).1
      change a.randomHead + 1 ≤ bits.length
      omega

/-- A finite path observes precisely the random interval between its initial
and final cursors. The unused suffix can be replaced arbitrarily. -/
theorem Steps.change_bits {data : InputData I A} {bits : BitString}
    {a b : BankConfiguration O Q S k} {t : ℕ} (path : B.Steps data bits a t b) (other : BitString)
    (same : ∀ i, a.randomHead ≤ i → i < b.randomHead → bits[i]? = other[i]?) :
    B.Steps data other a t b := by
  induction path with
  | refl => exact .refl _
  | step a next write work input auxiliary index emit t b table rest ih =>
      exact .step _ _ _ _ _ _ _ _ _ _ table (ih same)
  | random a no yes bit t b table lookup rest ih =>
      have increased := rest.random_monotone B
      change a.randomHead + 1 ≤ b.randomHead at increased
      have lookup' : other[a.randomHead]? = some bit :=
        (same a.randomHead le_rfl (by omega)).symm.trans lookup
      apply Steps.random a no yes bit t b table lookup'
      apply ih
      intro i lower upper
      apply same i (by change a.randomHead + 1 ≤ i at lower; omega) upper

/-- Concatenate a new suffix at the exact number of consumed bits. -/
theorem Steps.replace_suffix {data : InputData I A} {bits : BitString}
    {a b : BankConfiguration O Q S k} {t : ℕ} (path : B.Steps data bits a t b)
    (bound : b.randomHead ≤ bits.length) (suffix : BitString) :
    B.Steps data (bits.take b.randomHead ++ suffix) a t b := by
  apply path.change_bits B
  intro i _ upper
  rw [List.getElem?_append_left (by simp [List.length_take, Nat.min_eq_left bound]; exact upper)]
  simp [List.getElem?_take, upper]

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
