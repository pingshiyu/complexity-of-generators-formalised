import ComplexityOfGenerators.Simulation.StackSpace.Loading

/-!
# Space-preserving compilation of Mathlib stack deciders

This is an operational bridge to the project's original `PSPACE` definition.
It includes loading the read-only input, intermediate compiler phases, final
verdicts, and the native visited-cell accounting. The number of source steps
is unrestricted.
-/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Fintype S] [Fintype Q] [Fintype V]
variable (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)

def machine : Machine S Bool Unit := TransducerBank.bankMachine (bank P entry initial answer)

theorem native_terminal (word : List S) (bits : BitString) (s : ℕ) (large : word.length + 1 ≤ s)
    (bounded : ∀ c, TM2.Reaches P (sourceInitial entry initial word) c → ∀ j, (c.stk j).length ≤ s)
    (finish : TM2.Cfg (fun _ : Fin (k + 1) => S) Q V)
    (path : TM2.Reaches P (sourceInitial entry initial word) finish) (halted : finish.l = none) :
    ∃ ticks last,
      (machine P entry initial answer).Steps (decisionData word) bits
        (machine P entry initial answer).initialConfiguration ticks last ∧
      (machine P entry initial answer).observe (decisionData word) bits last =
        .halted (if answer finish.var then .accepted [] else .rejected) ∧
      (machine P entry initial answer).InRegion (s + programCost P) last := by
  let B := bank P entry initial answer
  obtain ⟨loaded, related, boot, region⟩ := TransducerBank.bank_loaded_inRegion B (decisionData word) bits
    (s + programCost P)
  have run := run_inRegion P entry initial answer word bits s large bounded finish path halted
  obtain ⟨ticks, last, tail, terminal, bound⟩ := run.compile B (fun _ => false) loaded related region
  exact ⟨1 + ticks, last, boot.trans _ tail, terminal, bound⟩

/-- A finite Mathlib stack program with polynomially bounded reachable stacks
compiles to a decider in the retained native model. The input is pushed onto
stack zero, so its initial stack is the reverse of the input word. -/
theorem mem_pspace (L : Language S) (space : PolynomialBound)
    (bounded : ∀ word c, TM2.Reaches P (sourceInitial entry initial word) c →
      ∀ j, (c.stk j).length ≤ space word.length)
    (terminates : ∀ word, ∃ finish,
      TM2.Reaches P (sourceInitial entry initial word) finish ∧ finish.l = none ∧
      (answer finish.var = true ↔ word ∈ L)) : L ∈ PSPACE S := by
  let M := machine P entry initial answer
  let p := PolynomialBound.ofPolynomial (2 * (space.asPolynomial + Polynomial.X + 1 +
    Polynomial.C (programCost P)) + 1)
  have complete (word : List S) (bits : BitString) : ∃ ticks last verdict,
      M.Steps (decisionData word) bits M.initialConfiguration ticks last ∧
      M.observe (decisionData word) bits last = .halted (if verdict then .accepted [] else .rejected) ∧
      last.visited.card ≤ p word.length ∧ (verdict = true ↔ word ∈ L) := by
    obtain ⟨finish, path, halted, correct⟩ := terminates word
    obtain ⟨ticks, last, run, terminal, region⟩ := native_terminal P entry initial answer word bits
      (space word.length + word.length + 1) (by omega)
      (fun c reachable j => (bounded word c reachable j).trans (by omega)) finish path halted
    refine ⟨ticks, last, answer finish.var, run, terminal, (region.card_le M).trans ?_, correct⟩
    have bound := PolynomialBound.eval_le_ofPolynomial
      (2 * (space.asPolynomial + Polynomial.X + 1 + Polynomial.C (programCost P)) + 1) word.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, PolynomialBound.asPolynomial_eval] at bound
    exact bound
  have runs (word : List S) (bits : BitString) : ∃ ticks verdict,
      M.run (decisionData word) bits ticks = .halted (if verdict then .accepted [] else .rejected) ∧
      (verdict = true ↔ word ∈ L) := by
    obtain ⟨ticks, last, verdict, path, terminal, _, correct⟩ := complete word bits
    exact ⟨ticks, verdict, by rw [← Machine.runFrom_initial, path.runFrom M, terminal], correct⟩
  refine ⟨M, p, TransducerBank.bankMachine_deterministic _ (bank_deterministic P entry initial answer),
    ?_, ?_, ?_⟩
  · intro word
    obtain ⟨ticks, verdict, run, _⟩ := runs word []
    exact ⟨ticks, _, run⟩
  · intro word
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
