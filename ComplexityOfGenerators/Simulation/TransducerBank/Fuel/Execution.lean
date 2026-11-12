import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Abort

/-! Every choice branch of the actual fuel controller terminates. The clock is
on a genuine extra tape; the theorem records both its primitive cost and that
accepted outputs came from a source execution within the supplied clock. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem bounded_execution (data : InputData I A) (bits : BitString)
    (fuel remaining used r : ℕ) (source : BankConfiguration O Q S k)
    (bounds : B.Bounded data r source) (capacity : used + remaining = fuel) :
    ∃ ticks result, ticks ≤ 3 * remaining + 1 ∧
      (bank B).Executes data bits (configuration B fuel used source) ticks result ∧
      (∀ word, result = .accepted word → ∃ sourceTicks, sourceTicks ≤ remaining ∧
        B.Executes data bits source sourceTicks (.accepted word)) := by
  induction remaining generalizing used r source with
  | zero =>
    have ended : used = fuel := by omega
    subst used
    cases action : B.instruction data source with
    | accept =>
      refine ⟨0, .accepted source.output, by omega, .accept _ ?_, ?_⟩
      · rw [fetch_instruction B data fuel fuel source, action]
      · intro word same
        cases same
        exact ⟨0, le_rfl, .accept source action⟩
    | reject =>
      refine ⟨0, .rejected, by omega, .reject _ ?_, ?_⟩
      · rw [fetch_instruction B data fuel fuel source, action]
      · intro word impossible; cases impossible
    | readRandom no yes =>
      refine ⟨1, .rejected, by omega,
        random_abort B data bits fuel r source bounds no yes action, ?_⟩
      intro word impossible; cases impossible
    | step next write work input auxiliary index emit =>
      refine ⟨1, .rejected, by omega,
        step_abort B data bits fuel r source bounds next write work input auxiliary index emit action, ?_⟩
      intro word impossible; cases impossible
  | succ remaining ih =>
    have live : used < fuel := by omega
    cases action : B.instruction data source with
    | accept =>
      refine ⟨0, .accepted source.output, by omega, .accept _ ?_, ?_⟩
      · rw [fetch_instruction B data fuel used source, action]
      · intro word same
        cases same
        exact ⟨0, Nat.zero_le _, .accept source action⟩
    | reject =>
      refine ⟨0, .rejected, by omega, .reject _ ?_, ?_⟩
      · rw [fetch_instruction B data fuel used source, action]
      · intro word impossible; cases impossible
    | step next write work input auxiliary index emit =>
      obtain ⟨ticks, result, cost, execution, sound⟩ :=
        ih (used + 1) (r + 1) (B.advance data source next write work input auxiliary index emit)
          (B.advance_bounded data r source next write work input auxiliary index emit bounds) (by omega)
      have path := step_path B data bits fuel used r source bounds
        next write work input auxiliary index emit action live
      refine ⟨3 + ticks, result, by omega, path.executes (bank B) execution, ?_⟩
      intro word accepted
      obtain ⟨sourceTicks, small, sourceExecution⟩ := sound word accepted
      exact ⟨sourceTicks + 1, by omega,
        .step source next write work input auxiliary index emit sourceTicks (.accepted word)
          action sourceExecution⟩
    | readRandom no yes =>
      cases lookup : bits[source.randomHead]? with
      | none =>
        have path := random_ready_path B data bits fuel used r source bounds no yes action live
        have exhausted : (bank B).Executes data bits
            {configuration B fuel (used + 1) source with state := .random no yes} 0 .exhausted :=
          .exhausted _ (.fetch no) (.fetch yes)
            (random_instruction B data fuel (used + 1) source no yes) lookup
        refine ⟨2, .exhausted, by omega, path.executes (bank B) exhausted, ?_⟩
        intro word impossible; cases impossible
      | some bit =>
        obtain ⟨ticks, result, cost, execution, sound⟩ :=
          ih (used + 1) (r + 1) (TapeBank.choose source (if bit then yes else no))
            (B.choose_bounded data r source _ bounds) (by omega)
        have path := random_path B data bits fuel used r source bounds no yes action live bit lookup
        refine ⟨3 + ticks, result, by omega, path.executes (bank B) execution, ?_⟩
        intro word accepted
        obtain ⟨sourceTicks, small, sourceExecution⟩ := sound word accepted
        exact ⟨sourceTicks + 1, by omega,
          .random source no yes bit sourceTicks (.accepted word) action lookup sourceExecution⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
