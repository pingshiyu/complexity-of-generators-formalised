import ComplexityOfGenerators.Simulation.LibraryTM.Execution
import ComplexityOfGenerators.Foundations.ResourceBounds
import ComplexityOfGenerators.Proofs.NativeSpaceCompilation

/-! Space-preserving compilation from actual library deciders, including input
loading, all intermediate phases, halting, and the final verdict. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM

open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (M : Complexity.TM n)

def machine : Machine Bool Bool Unit := bankMachine (bank M)

theorem native_terminal (L : Language Bool) (S : ℕ → ℕ) (decides : M.DecidesInSpace L S)
    (word : BitString) (bits : BitString) :
    ∃ ticks finish verdict,
      (machine M).Steps (decisionData word) bits (machine M).initialConfiguration ticks finish ∧
      (machine M).observe (decisionData word) bits finish =
        .halted (if verdict then .accepted [] else .rejected) ∧
      finish.visited.card ≤ 4 * (word.length + S word.length + n + 4) + 1 ∧
      (verdict = true ↔ word ∈ L) := by
  obtain ⟨source, path, halt, yes, no⟩ := decides.2 word
  have run := run_inRegion M word bits (S word.length) (decides.1 word) source path halt
  obtain ⟨loaded, ready, boot, region⟩ := bank_loaded_inRegion (bank M) (decisionData word) bits
    (radius word.length (S word.length) n)
  obtain ⟨ticks, finish, tail, terminal, bounded⟩ := run.compile (bank M) (fun _ => false) loaded ready region
  refine ⟨1 + ticks, finish, decide (source.output.cells 1 = .one), boot.trans _ tail, ?_, ?_, ?_⟩
  · simpa [machine] using terminal
  · have size := bounded.card_le (machine M)
    unfold radius at size
    omega
  · by_cases member : word ∈ L
    · simp [yes member, member]
    · simp [no member, member]

theorem machine_spaceBound (L : Language Bool) (S : ℕ → ℕ) (decides : M.DecidesInSpace L S)
    (word : BitString) :
    (machine M).SpaceBound (decisionData word) (4 * (word.length + S word.length + n + 4) + 1) := by
  apply Machine.spaceBound_of_terminal_paths
  intro bits
  obtain ⟨ticks, finish, verdict, path, terminal, size, _⟩ := native_terminal M L S decides word bits
  exact ⟨ticks, finish, _, path, terminal, size⟩

theorem native_run (L : Language Bool) (S : ℕ → ℕ) (decides : M.DecidesInSpace L S)
    (word : BitString) (bits : BitString) :
    ∃ ticks verdict, (machine M).run (decisionData word) bits ticks =
      .halted (if verdict then .accepted [] else .rejected) ∧ (verdict = true ↔ word ∈ L) := by
  obtain ⟨ticks, finish, verdict, path, terminal, _, correct⟩ := native_terminal M L S decides word bits
  exact ⟨ticks, verdict, by rw [← Machine.runFrom_initial, path.runFrom _, terminal], correct⟩

/-- A library machine with an everywhere polynomial space bound gives a native
decider. The generated machine depends only on the fixed source transition table. -/
theorem mem_pspace (L : Language Bool) (S : ℕ → ℕ) (decides : M.DecidesInSpace L S)
    (p : PolynomialBound) (bound : ∀ m, S m ≤ p m) : L ∈ PSPACE Bool := by
  let space := PolynomialBound.ofPolynomial
    (4 * (Polynomial.X + p.asPolynomial + Polynomial.C (n + 4)) + 1)
  apply mem_pspace_of_encoded_terminal_paths (machine M) id L space
    (bankMachine_deterministic _ (deterministic M))
  intro word bits
  obtain ⟨ticks, finish, verdict, path, terminal, size, correct⟩ := native_terminal M L S decides word bits
  simp only [List.map_id]
  refine ⟨ticks, finish, verdict, path, terminal, size.trans ?_, correct⟩
  have polynomial := PolynomialBound.eval_le_ofPolynomial
    (4 * (Polynomial.X + p.asPolynomial + Polynomial.C (n + 4)) + 1) word.length
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, PolynomialBound.asPolynomial_eval] at polynomial
  dsimp [space]
  have := bound word.length
  omega

end
end ComplexityOfGenerators.Simulation.LibraryTM
