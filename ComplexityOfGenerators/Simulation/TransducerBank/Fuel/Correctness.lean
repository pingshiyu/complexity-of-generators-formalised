import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- Every source acceptance that fits in the real clock remains possible, with
exactly three microsteps per nonterminal source transition. -/
theorem accepted_executes (data : InputData I A) (bits : BitString)
    (fuel ticks used r : ℕ) (source : BankConfiguration O Q S k) (word : Word O)
    (bounds : B.Bounded data r source)
    (execution : B.Executes data bits source ticks (.accepted word))
    (capacity : used + ticks ≤ fuel) :
    (bank B).Executes data bits (configuration B fuel used source) (3 * ticks) (.accepted word) := by
  induction ticks generalizing used r source with
  | zero =>
      cases execution with
      | accept source action =>
          exact .accept _ (by rw [fetch_instruction B data fuel used source, action])
  | succ ticks ih =>
      have live : used < fuel := by omega
      cases execution with
      | random source no yes bit ticks result action lookup rest =>
          have next := ih (used + 1) (r + 1) (TapeBank.choose source (if bit then yes else no))
            (B.choose_bounded data r source _ bounds) rest (by omega)
          have path := random_path B data bits fuel used r source bounds no yes action live bit lookup
          have actual := path.executes (bank B) next
          simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using actual
      | step source next write work input auxiliary index emit ticks result action rest =>
          have tail := ih (used + 1) (r + 1)
            (B.advance data source next write work input auxiliary index emit)
            (B.advance_bounded data r source next write work input auxiliary index emit bounds)
            rest (by omega)
          have path := step_path B data bits fuel used r source bounds next write work
            input auxiliary index emit action live
          have actual := path.executes (bank B) tail
          simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using actual

/-- Accepted outputs are exactly those produced before the unary clock runs out.
The preloaded clock is explicit in the start configuration and has not been
silently supplied as ordinary-input advice. -/
theorem accepted_iff (data : InputData I A) (bits : BitString) (fuel r : ℕ)
    (source : BankConfiguration O Q S k) (word : Word O) (bounds : B.Bounded data r source) :
    (∃ ticks, (bank B).Executes data bits (configuration B fuel 0 source) ticks (.accepted word)) ↔
      ∃ ticks, ticks ≤ fuel ∧ B.Executes data bits source ticks (.accepted word) := by
  constructor
  · rintro ⟨ticks, execution⟩
    obtain ⟨otherTicks, result, _, other, sound⟩ :=
      bounded_execution B data bits fuel fuel 0 r source bounds (by omega)
    have same := (TapeBank.Executes.unique (bank B) execution other).2
    exact sound word same.symm
  · rintro ⟨ticks, small, execution⟩
    exact ⟨3 * ticks, accepted_executes B data bits fuel ticks 0 r source word bounds
      execution (by omega)⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
