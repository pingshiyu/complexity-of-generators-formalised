import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped.Drain
import ComplexityOfGenerators.Proofs.GeneratorCriteria

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

open TransducerBank
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ}
variable [Fintype I] [Fintype A] [Fintype O] [Fintype Q] [Fintype S]
variable (B : TapeBank I A O Q S k) (counter : Fin k)

noncomputable def machine : Machine I A O := TransducerBank.bankMachine (bank B counter)

def compileBudget (index bodyTicks : ℕ) : ℕ :=
  let total := 4 * index + 4 + bodyTicks
  1 + (total + 1) * (2 * total + 4)

/-- Successful input checks have linear cost in the unary index, regardless
of the lengths of other words on which the same machine may be invoked. -/
theorem run_compiled (data : InputData I A) (bits : BitString)
    (input : data.input.length ≤ data.index) (auxiliary : data.auxiliary.length ≤ data.index)
    (bodyTicks : ℕ) (result : Outcome O)
    (body : B.Executes data bits B.initialConfiguration bodyTicks result) :
    ∃ ticks, ticks ≤ compileBudget data.index bodyTicks ∧
      (machine B counter).run data bits ticks = .halted result := by
  have checked :=  checked_prefix B counter data bits input auxiliary
  have execution := checked.executes _ (body_executes B counter data bits body)
  obtain ⟨ticks, bound, run⟩ := TransducerBank.bank_run (bank B counter) data bits _ result execution
  refine ⟨ticks, bound.trans ?_, run⟩
  unfold compileBudget
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul <;> omega

theorem oversized_run (data : InputData I A) (bits : BitString)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    ∃ ticks, ticks ≤ compileBudget data.index bits.length ∧
      (machine B counter).run data bits ticks = .halted .exhausted := by
  obtain ⟨ticks, sourceBound, execution⟩ := oversized_executes B counter data bits oversized
  obtain ⟨nativeTicks, bound, run⟩ := TransducerBank.bank_run (bank B counter) data bits ticks .exhausted execution
  refine ⟨nativeTicks, bound.trans ?_, run⟩
  unfold compileBudget
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul <;> omega

theorem oversized_language (data : InputData I A)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    (machine B counter).generatedLanguage data = ∅ := by
  ext word
  constructor
  · rintro ⟨bits, _, ticks, accepts⟩
    obtain ⟨drainTicks, _, exhausted⟩ := oversized_run B counter data bits oversized
    have impossible := (machine B counter).halted_outcome_unique data bits ticks drainTicks
      (.accepted word) .exhausted accepts exhausted
    cases impossible
  · intro impossible; exact False.elim impossible

theorem compileBudget_mono {n t u : ℕ} (bound : t ≤ u) :
    compileBudget n t ≤ compileBudget n u := by
  unfold compileBudget
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul <;> omega

theorem oversized_isGenerator (data : InputData I A)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    (machine B counter).IsGenerator data := by
  refine ⟨⟨?_, ?_⟩, Or.inr ?_⟩
  · intro bits
    obtain ⟨ticks, _, run⟩ := oversized_run B counter data bits oversized
    exact ⟨ticks, .exhausted, run⟩
  · intro bits ticks rejects
    obtain ⟨drainTicks, _, exhausted⟩ := oversized_run B counter data bits oversized
    have impossible := (machine B counter).halted_outcome_unique data bits ticks drainTicks
      .rejected .exhausted rejects exhausted
    cases impossible
  · rw [(machine B counter).acceptedStreams_eq_empty_iff data |>.mpr
      (oversized_language B counter data oversized)]
    exact MeasureTheory.measure_empty

theorem oversized_trial (data : InputData I A) (seed : ℕ)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    (machine B counter).GeneratorTimeBound data seed (compileBudget data.index seed) := by
  constructor
  · intro bits length
    obtain ⟨ticks, bound, run⟩ := oversized_run B counter data bits oversized
    have totalBound := bound.trans (compileBudget_mono length)
    refine ⟨.exhausted, ?_⟩
    have extended := (machine B counter).run_halted_add data bits ticks .exhausted run
      (compileBudget data.index seed - ticks)
    simpa only [Nat.add_sub_of_le totalBound] using extended
  · intro bits length
    rw [oversized_language B counter data oversized]
    constructor
    · rintro ⟨word, ticks, accepts⟩
      obtain ⟨drainTicks, _, exhausted⟩ := oversized_run B counter data bits oversized
      have impossible := (machine B counter).halted_outcome_unique data bits ticks drainTicks
        (.accepted word) .exhausted accepts exhausted
      cases impossible
    · intro empty
      exact False.elim (Set.not_nonempty_empty empty)

end ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped
