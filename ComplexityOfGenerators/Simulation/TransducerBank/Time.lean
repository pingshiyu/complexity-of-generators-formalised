import ComplexityOfGenerators.Simulation.TransducerBank.Random
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! Quantitative compilation of finite transducer banks into native machines.
The bound includes initialization, random reads, output steps, all virtual-head
scans, and terminal lookup. No whole-tape operation is a primitive. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

theorem bank_simulates (data : InputData I A) (bits : BitString) (source : BankConfiguration O Q S k)
    (t : ℕ) (result : Outcome O) (exec : B.Executes data bits source t result)
    (r : ℕ) (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded data r source) :
    ∃ ticks, ticks ≤ (t + 1) * (2 * (r + t) + 4) ∧
      (bankMachine B).runFrom data bits start ticks = .halted result := by
  induction exec generalizing r negative start with
  | accept source table =>
      refine ⟨(source.head (B.select source.state)).natAbs, ?_, ?_⟩
      · have := bounded.head (B.select source.state)
        omega
      · exact bank_terminal B data bits r source negative start h bounded _ (Or.inl ⟨table, rfl⟩)
  | reject source table =>
      refine ⟨(source.head (B.select source.state)).natAbs, ?_, ?_⟩
      · have := bounded.head (B.select source.state)
        omega
      · exact bank_terminal B data bits r source negative start h bounded _ (Or.inr (Or.inl ⟨table, rfl⟩))
  | exhausted source no yes table absent =>
      refine ⟨(source.head (B.select source.state)).natAbs, ?_, ?_⟩
      · have := bounded.head (B.select source.state)
        omega
      · exact bank_terminal B data bits r source negative start h bounded _ (Or.inr (Or.inr ⟨no, yes, table, absent, rfl⟩))
  | random source no yes bit t result table lookup rest ih =>
      obtain ⟨s, ready, cost, related, run⟩ := bank_random B data bits r source negative start h bounded no yes bit table lookup
      obtain ⟨u, cost', run'⟩ := ih (r + 1) negative ready related
        (B.choose_bounded data r source _ bounded)
      refine ⟨s + u, ?_, ?_⟩
      · calc
          s + u ≤ (2 * r + 4) + (t + 1) * (2 * (r + 1 + t) + 4) := Nat.add_le_add cost cost'
          _ ≤ (t + 1 + 1) * (2 * (r + (t + 1)) + 4) := by nlinarith
      · rw [(bankMachine B).runFrom_add _ _ _ ready _ run]
        exact run'
  | step source next write work input auxiliary index emit t result table rest ih =>
      obtain ⟨s, ready, sides, cost, related, run⟩ :=
        bank_step B data bits r source negative start h bounded next write work input auxiliary index emit table
      obtain ⟨u, cost', run'⟩ := ih (r + 1) sides ready related
        (B.advance_bounded data r source next write work input auxiliary index emit bounded)
      refine ⟨s + u, ?_, ?_⟩
      · calc
          s + u ≤ (2 * r + 4) + (t + 1) * (2 * (r + 1 + t) + 4) := Nat.add_le_add cost cost'
          _ ≤ (t + 1 + 1) * (2 * (r + (t + 1)) + 4) := by nlinarith
      · rw [(bankMachine B).runFrom_add _ _ _ ready _ run]
        exact run'

/-- End-to-end simulation starts from the native blank work tape. -/
theorem bank_run (data : InputData I A) (bits : BitString) (t : ℕ) (result : Outcome O)
    (exec : B.Executes data bits B.initialConfiguration t result) :
    ∃ ticks, ticks ≤ 1 + (t + 1) * (2 * t + 4) ∧
      (bankMachine B).run data bits ticks = .halted result := by
  obtain ⟨ready, related, loaded⟩ := bank_loaded B data bits
  obtain ⟨u, cost, run⟩ := bank_simulates B data bits B.initialConfiguration t result exec
    0 (fun _ => false) ready related (B.initial_bounded data)
  refine ⟨1 + u, by simpa using Nat.add_le_add_left cost 1, ?_⟩
  rw [← (bankMachine B).runFrom_initial] at loaded ⊢
  rw [(bankMachine B).runFrom_add _ _ _ ready _ loaded]
  exact run

end
end ComplexityOfGenerators.Simulation.TransducerBank
