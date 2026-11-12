import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Trace
import ComplexityOfGenerators.Foundations.FiniteBlockPhases

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

theorem drop_prepend (front bits : BitString) (offset : ℕ) :
    (front++bits).drop (front.length+offset) = bits.drop offset := by
  rw [List.drop_append]
  simp only [List.drop_eq_nil_of_le (by omega : front.length ≤ front.length+offset), List.nil_append,
    Nat.add_sub_cancel_left]

theorem Trace.prepend {bits : BitString} {offset : ℕ} {parts : List ℕ} {records : List (Record α)}
    (trace : Trace P bits offset parts records) (front : BitString) :
    Trace P (front++bits) (front.length+offset) parts records := by
  induction parts generalizing offset records with
  | nil => cases records <;> simpa [Trace] using trace
  | cons j parts ih =>
      cases records with
      | nil => exact False.elim trace
      | cons record records =>
          obtain ⟨enough, failed, success, later⟩ := trace
          refine ⟨by simp only [List.length_append]; omega, ?_, ?_, ?_⟩
          · intro k less
            rw [Nat.add_assoc, drop_prepend]
            exact failed k less
          · rw [Nat.add_assoc, drop_prepend]
            exact success
          · simpa only [Nat.add_assoc] using ih later

/-- Every indexed list of source words has a concrete first-try trace. The
native witness contains exactly one full bounded source block per factor. -/
theorem trace_witness (parts : List ℕ) (factors : List (List α))
    (language : List.Forall₂ (fun j word => word ∈ P.layer j) parts factors) :
    ∃ bits records, Trace P bits 0 parts records ∧ words records = factors.flatten ∧
      blocks records = parts.length ∧ bits.length = consumed P parts records := by
  induction language with
  | nil => exact ⟨[], [], trivial, rfl, rfl, rfl⟩
  | @cons j word parts factors member language ih =>
      obtain ⟨tail, records, trace, output, number, length⟩ := ih
      obtain ⟨vector, hit⟩ := (P.layer_iff j word).mp member
      let block := List.ofFn vector
      have size : block.length = P.seed j := by simp [block]
      let record : Record α := ⟨0, word⟩
      have shifted : Trace P (block++tail) (P.seed j) parts records := by
        simpa only [size, Nat.add_zero] using Trace.prepend P trace block
      refine ⟨block++tail, record::records, ?_, ?_, ?_, ?_⟩
      · refine ⟨by simp [record, Record.blocks, size], ?_, ?_, ?_⟩
        · intro k less; exact False.elim (Nat.not_lt_zero k less)
        · have taken : (block++tail).take (P.seed j) = block := by rw [← size, List.take_left]
          change UnionGenerator.sourceValue P.machine P.clock j
            ((block++tail).drop (0+0*P.seed j) |>.take (P.seed j)) = some word
          simp only [Nat.zero_add, Nat.zero_mul, List.drop_zero]
          rw [taken]
          exact hit
        · simpa [record, Record.blocks] using shifted
      · change word++words records = word++factors.flatten
        rw [output]
      · change record.blocks+blocks records = parts.length+1
        rw [number]
        simp [record, Record.blocks, Nat.add_comm]
      · simp [consumed, record, Record.blocks, size, length]

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
