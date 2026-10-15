import ComplexityOfGenerators.Simulation.StackSpace.Trace
import ComplexityOfGenerators.Foundations.InputAlphabet

/-! Compile stack programs whose work alphabet contains an encoding of the
input alphabet. Only encoded inputs need a source trace: no behaviour on
unreachable malformed encodings is assumed. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I S Q V : Type} {k : ℕ} [Fintype I] [Fintype S] [Fintype Q] [Fintype V]

/-- The finite-control compiler with a letterwise input adapter. The adapter
preserves word length and adds no work cells or execution steps. -/
theorem mem_pspace_of_encoded_trace
    (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
    (encode : I → S) (L : Language I) (space : PolynomialBound)
    (executes : ∀ word : Word I, ∃ finish,
      Trace P (space word.length) (sourceInitial entry initial (word.map encode)) finish ∧
      finish.l = none ∧ (answer finish.var = true ↔ word ∈ L)) : L ∈ PSPACE I := by
  let source := machine P entry initial answer
  let M := source.mapInput encode
  let p := PolynomialBound.ofPolynomial
    (2 * (space.asPolynomial + Polynomial.X + 1 + Polynomial.C (programCost P)) + 1)
  have complete (word : Word I) (bits : BitString) : ∃ ticks last verdict,
      source.Steps (decisionData (word.map encode)) bits source.initialConfiguration ticks last ∧
      source.observe (decisionData (word.map encode)) bits last =
        .halted (if verdict then .accepted [] else .rejected) ∧
      last.visited.card ≤ p word.length ∧ (verdict = true ↔ word ∈ L) := by
    obtain ⟨finish, path, halted, correct⟩ := executes word
    obtain ⟨ticks, last, run, terminal, region⟩ := native_terminal P entry initial answer (word.map encode) bits
      (space word.length + word.length + 1) (by simp <;> omega)
      (fun c reachable j => (path.bounds_reachable halted c reachable j).trans (by omega))
      finish path.reaches halted
    refine ⟨ticks, last, answer finish.var, run, terminal, (region.card_le source).trans ?_, correct⟩
    have bound := PolynomialBound.eval_le_ofPolynomial
      (2 * (space.asPolynomial + Polynomial.X + 1 + Polynomial.C (programCost P)) + 1) word.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, PolynomialBound.asPolynomial_eval] at bound
    exact bound
  have runs (word : Word I) (bits : BitString) : ∃ ticks verdict,
      M.run (decisionData word) bits ticks = .halted (if verdict then .accepted [] else .rejected) ∧
      (verdict = true ↔ word ∈ L) := by
    obtain ⟨ticks, last, verdict, path, terminal, _, correct⟩ := complete word bits
    refine ⟨ticks, verdict, ?_, correct⟩
    apply (source.mapInput_run_halted_iff encode (decisionData word) bits ticks _).mpr
    change source.run (decisionData (word.map encode)) bits ticks = _
    rw [← Machine.runFrom_initial, path.runFrom source, terminal]
  refine ⟨M, p, source.mapInput_deterministic encode
    (TransducerBank.bankMachine_deterministic _ (bank_deterministic P entry initial answer)), ?_, ?_, ?_⟩
  · intro word
    obtain ⟨ticks, verdict, run, _⟩ := runs word []
    exact ⟨ticks, _, run⟩
  · intro word
    apply source.mapInput_spaceBound encode
    apply Machine.spaceBound_of_terminal_paths
    intro bits
    obtain ⟨ticks, last, verdict, path, terminal, size, _⟩ := complete word bits
    exact ⟨ticks, last, _, path, terminal, size⟩
  · intro word
    obtain ⟨ticks, verdict, run, correct⟩ := runs word []
    constructor
    · rintro ⟨out, t, accepted⟩
      have same := M.halted_outcome_unique _ _ _ _ _ _ accepted run
      cases verdict <;> simp_all
    · intro member
      exact ⟨[], ticks, by simpa [correct.mpr member] using run⟩

end
end ComplexityOfGenerators.Simulation.StackSpace
