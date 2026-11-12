import ComplexityOfGenerators.Simulation.FixedBlockRetry.Value
import ComplexityOfGenerators.Foundations.FixedBlockPrefix

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
variable {O : Type}

theorem dropped_block (width : ℕ) (bits : BitString) (j : ℕ) :
    ((bits.drop width).drop (j*width)).take width = (bits.drop ((j+1)*width)).take width := by
  rw [List.drop_drop]
  congr 2
  ring

/-- A designated successful phase is returned if every earlier phase failed. -/
theorem scan_first_success (width : ℕ) (phase : BitString → Option (List O))
    (count i : ℕ) (bits : BitString) (word : List O) (index : i < count)
    (earlier : ∀ j < i, phase ((bits.drop (j*width)).take width) = none)
    (hit : phase ((bits.drop (i*width)).take width) = some word) :
    scan width phase count bits = some word := by
  induction count generalizing i bits with
  | zero => omega
  | succ count ih =>
    cases i with
    | zero =>
      have first : phase (bits.take width) = some word := by simpa only [Nat.zero_mul, List.drop_zero] using hit
      rw [scan, first, Option.some_or]
    | succ i =>
      have first := earlier 0 (by omega)
      simp only [Nat.zero_mul, List.drop_zero] at first
      rw [scan, first, Option.none_or]
      apply ih i (bits.drop width) (by omega)
      · intro j before
        rw [dropped_block]
        exact earlier (j+1) (by omega)
      · rw [dropped_block]
        exact hit

/-- Every selected word comes from one of the attempted blocks. -/
theorem scan_sound (width : ℕ) (phase : BitString → Option (List O))
    (count : ℕ) (bits : BitString) (word : List O) (output : scan width phase count bits = some word) :
    ∃ j < count, phase ((bits.drop (j*width)).take width) = some word := by
  induction count generalizing bits with
  | zero => simp [scan] at output
  | succ count ih =>
    cases first : phase (bits.take width) with
    | none =>
      have rest : scan width phase count (bits.drop width) = some word := by simpa [scan, first] using output
      obtain ⟨j, bound, hit⟩ := ih _ rest
      exact ⟨j+1, by omega, by rwa [← dropped_block]⟩
    | some value =>
      have equal : value = word := by simpa [scan, first] using output
      exact ⟨0, by omega, by simpa [equal] using first⟩

theorem value_sound (width : PolynomialBound) (phase : ℕ → BitString → Option (List O))
    (n : ℕ) (bits : BitString) (word : List O) (output : value width phase n bits = some word) :
    ∃ block : BitString, block.length = width n ∧ phase n block = some word := by
  obtain ⟨j, index, hit⟩ := scan_sound (width n) (phase n) _ bits word output
  have product := Nat.div_mul_le_self bits.length (width n)
  have before : (j+1)*width n ≤ (bits.length/width n)*width n :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨(bits.drop (j*width n)).take (width n), ?_, hit⟩
  have full : j*width n+width n ≤ bits.length := by nlinarith
  simp only [List.length_take, List.length_drop]
  omega

theorem value_single_block (width : PolynomialBound) (phase : ℕ → BitString → Option (List O))
    (n : ℕ) (block : BitString) (length : block.length = width n) :
    value width phase n block = phase n block := by
  unfold value
  rw [length, Nat.div_self (width.positive n)]
  have take : block.take (width n) = block := by rw [← length, List.take_length]
  simp only [scan, take, Option.or_none]

def successSet (width : PolynomialBound) (phase : ℕ → BitString → Option (List O)) (n : ℕ) :
    Set (Fin (width n) → Bool) := {block | (phase n (List.ofFn block)).isSome}

theorem value_first_success_prefix (width : PolynomialBound) (phase : ℕ → BitString → Option (List O))
    (n : ℕ) (stream : BitStream)
    (hit : fixedBlock (width n) stream (firstSuccessIndex (width n) (successSet width phase n) stream) ∈
      successSet width phase n) :
    ∃ word, value width phase n
      (streamPrefix stream ((firstSuccessIndex (width n) (successSet width phase n) stream+1)*width n)) = some word ∧
      phase n (List.ofFn (fixedBlock (width n) stream (firstSuccessIndex (width n) (successSet width phase n) stream))) = some word := by
  let N := firstSuccessIndex (width n) (successSet width phase n) stream
  have prior : ∀ j < N, fixedBlock (width n) stream j ∉ successSet width phase n := by
    rcases firstSuccessIndex_spec (width n) (successSet width phase n) stream with ⟨_, minimal⟩ | ⟨_, never⟩
    · exact minimal
    · exact fun j _ => never j
  obtain ⟨word, output⟩ := Option.isSome_iff_exists.mp hit
  refine ⟨word, ?_, output⟩
  change scan (width n) (phase n)
    ((streamPrefix stream ((N+1)*width n)).length/width n) _ = some word
  rw [streamPrefix_length, Nat.mul_div_cancel _ (width.positive n)]
  apply scan_first_success _ _ (N+1) N _ word (by omega)
  · intro j index
    rw [streamPrefix_drop_take_fixedBlock _ _ _ _ (by omega)]
    have absent := prior j index
    change ¬(phase n (List.ofFn (fixedBlock (width n) stream j))).isSome at absent
    cases result : phase n (List.ofFn (fixedBlock (width n) stream j)) <;> simp_all
  · rw [streamPrefix_drop_take_fixedBlock _ _ _ _ le_rfl]
    exact output

end ComplexityOfGenerators.Simulation.FixedBlockRetry
