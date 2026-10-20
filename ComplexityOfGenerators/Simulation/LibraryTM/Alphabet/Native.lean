import ComplexityOfGenerators.Simulation.LibraryTM.Alphabet.Execution
import ComplexityOfGenerators.Simulation.LibraryTM.Alphabet.Loading

/-! A library polynomial-space decider induces a native decider over any finite
alphabet. All input-copying and simulation cells count toward native space. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {n : ℕ} (M : Complexity.TM n)

def machine : Machine α Bool Unit := bankMachine (bank (α := α) M)

theorem native_terminal (L : Language Bool) (S : ℕ → ℕ) (decides : M.DecidesInSpace L S)
    (word : List α) (bits : BitString) :
    ∃ ticks finish verdict,
      (machine M).Steps (decisionData word) bits (machine M).initialConfiguration ticks finish ∧
      (machine M).observe (decisionData word) bits finish =
        .halted (if verdict then .accepted [] else .rejected) ∧
      finish.visited.card ≤ 8 * ((NativeNTM.encode word).length + S (NativeNTM.encode word).length + n + 4) + 1 ∧
      (verdict = true ↔ NativeNTM.encode word ∈ L) := by
  let full := NativeNTM.encode word
  let r := 4 * (full.length + S full.length + n + 4)
  obtain ⟨source, path, halt, yes, no⟩ := decides.2 full
  have simulation := (simulated_run M word bits (S full.length) (decides.1 full) source path halt).mono
    (bank M) (by dsimp [radius, r, full]; omega : radius full.length (S full.length) n ≤ r)
  have length := (NativeNTM.encode_length word).1
  have loader := ((load_initial M bits word).inRegion (bank M) 0 ((bank M).initial_bounded _)).mono
    (bank M) (by dsimp [r, full]; omega : 0 + (2 * full.length + word.length + 4) ≤ r)
  have run := simulation.prepend (bank M) loader
  obtain ⟨loaded, ready, boot, region⟩ := bank_loaded_inRegion (bank M) (decisionData word) bits r
  obtain ⟨ticks, finish, tail, terminal, bounded⟩ := run.compile (bank M) (fun _ => false) loaded ready region
  refine ⟨1 + ticks, finish, decide (source.output.cells 1 = .one), boot.trans _ tail, ?_, ?_, ?_⟩
  · simpa [machine] using terminal
  · have size := bounded.card_le (machine M)
    dsimp [r, full] at size
    omega
  · change decide (source.output.cells 1 = .one) = true ↔ full ∈ L
    by_cases member : full ∈ L
    · simp [yes member, member]
    · simp [no member, member]

theorem mem_pspace_preimage (L : Language Bool) (S : ℕ → ℕ) (decides : M.DecidesInSpace L S)
    (p : PolynomialBound) (bound : ∀ m, S m ≤ p m) :
    {word : List α | NativeNTM.encode word ∈ L} ∈ PSPACE α := by
  let linear : PolynomialBound := ⟨Fintype.card α + 1, 1, by omega⟩
  let q := 8 * (linear.asPolynomial + p.asPolynomial.comp linear.asPolynomial + Polynomial.C (n + 4)) + 1
  let space := PolynomialBound.ofPolynomial q
  apply mem_pspace_of_encoded_terminal_paths (machine (α := α) M) id _ space
    (bankMachine_deterministic _ (deterministic M))
  intro word bits
  obtain ⟨ticks, finish, verdict, path, terminal, size, correct⟩ := native_terminal M L S decides word bits
  simp only [List.map_id]
  refine ⟨ticks, finish, verdict, path, terminal, size.trans ?_, correct⟩
  have encoded : (NativeNTM.encode word).length ≤ linear word.length := by
    have length := (NativeNTM.encode_length word).2
    dsimp [linear, PolynomialBound.eval]
    simp only [pow_one]
    exact length.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have monotone : p (NativeNTM.encode word).length ≤ p (linear word.length) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right encoded 1) _)
  have upper := bound (NativeNTM.encode word).length
  have polynomial := PolynomialBound.eval_le_ofPolynomial q word.length
  simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp, PolynomialBound.asPolynomial_eval] at polynomial
  dsimp [space, q]
  omega

end
end ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
