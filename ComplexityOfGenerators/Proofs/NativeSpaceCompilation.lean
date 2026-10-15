import ComplexityOfGenerators.Simulation.TransducerBank.Space

/-!
# Polynomial-space decision by finite tape-bank programs

The compiler is the existing finite-control, single-work-tape construction.
Its space bound is now operational, independent of its time overhead. Applying
this result requires an actual finite program, termination, and a proved bound
on all its reachable virtual heads.
-/

namespace ComplexityOfGenerators

open Simulation.TransducerBank

noncomputable section

variable {α Q S : Type} {k : ℕ} [Fintype α] [Fintype Q] [Fintype S]

/-- A finite tape-bank decider with polynomial head radius gives a native
polynomial-space decider. Its running time may be arbitrarily large. -/
theorem mem_pspace_of_tapeBank (B : TapeBank α Bool Unit Q S k) (L : Language α)
    (radius : PolynomialBound) (deterministic : B.Deterministic)
    (space : ∀ word, B.SpaceBound (decisionData word) (radius word.length))
    (terminates : ∀ word, ∃ t, ∃ answer : Bool,
      B.Executes (decisionData word) [] B.initialConfiguration t
        (if answer then .accepted [] else .rejected) ∧ (answer = true ↔ word ∈ L)) :
    L ∈ PSPACE α := by
  let p := PolynomialBound.ofPolynomial (2 * radius.asPolynomial + 1)
  have runs (word : List α) (bits : BitString) :
      ∃ t, ∃ answer : Bool, (bankMachine B).run (decisionData word) bits t =
        .halted (if answer then .accepted [] else .rejected) ∧ (answer = true ↔ word ∈ L) := by
    obtain ⟨t, answer, exec, correct⟩ := terminates word
    obtain ⟨ticks, _, run⟩ := bank_run B (decisionData word) bits t _
      (exec.change_bits B deterministic bits)
    exact ⟨ticks, answer, run, correct⟩
  refine ⟨bankMachine B, p, bankMachine_deterministic B deterministic, ?_, ?_, ?_⟩
  · intro word
    obtain ⟨ticks, answer, run, _⟩ := runs word []
    exact ⟨ticks, _, run⟩
  · intro word
    apply Machine.SpaceBound.mono (bankMachine B)
      (bankMachine_spaceBound B (decisionData word) (radius word.length) (space word) ?_)
    · have bound := PolynomialBound.eval_le_ofPolynomial (2 * radius.asPolynomial + 1) word.length
      simpa using bound
    · intro bits
      obtain ⟨t, answer, exec, _⟩ := terminates word
      exact ⟨t, _, exec.change_bits B deterministic bits⟩
  · intro word
    obtain ⟨ticks, answer, run, correct⟩ := runs word []
    constructor
    · rintro ⟨output, t, accepted⟩
      have same := (bankMachine B).halted_outcome_unique _ _ _ _ _ _ accepted run
      cases answer <;> simp_all
    · intro member
      have yes := correct.mpr member
      exact ⟨[], ticks, by simpa [yes] using run⟩

end
end ComplexityOfGenerators
