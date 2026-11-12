import ComplexityOfGenerators.Proofs.BoundedPhaseFamilies
import ComplexityOfGenerators.Proofs.BoundedCommandPhase
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Execution
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.PhaseMeans
import ComplexityOfGenerators.Foundations.IndexedSupportClosure

namespace ComplexityOfGenerators.BoundedPhaseFamily
open Simulation WordStack MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P Q : BoundedPhaseFamily α)

def concatCode := ConcatenationGenerator.command P.machine Q.machine P.seed P.clock Q.seed Q.clock
  (ConcatenationGenerator.concatSeed P.seed Q.seed)
noncomputable def concatMachine := ((concatCode P Q).program 0).machine
noncomputable def concatClock := Program.compiledTime
  (ConcatenationGenerator.stackTime P.machine Q.machine P.seed P.clock Q.seed Q.clock (ConcatenationGenerator.concatSeed P.seed Q.seed))

theorem concatMachine_value (n : ℕ) (bits : BitString) (length : bits.length = ConcatenationGenerator.concatSeed P.seed Q.seed n) :
    UnionGenerator.sourceValue (concatMachine P Q) (concatClock P Q) n bits =
      ConcatenationGenerator.algorithm P.machine Q.machine P.seed P.clock Q.seed Q.clock n bits := by
  have actual := Command.bounded_sourceValue (concatCode P Q) 0 (ConcatenationGenerator.concatSeed P.seed Q.seed)
    (ConcatenationGenerator.stackTime P.machine Q.machine P.seed P.clock Q.seed Q.clock (ConcatenationGenerator.concatSeed P.seed Q.seed))
    (ConcatenationGenerator.commandValue P.machine Q.machine P.seed P.clock Q.seed Q.clock (ConcatenationGenerator.concatSeed P.seed Q.seed))
    (by
      intro index tape
      obtain ⟨t, _, result, run, output⟩ := ConcatenationGenerator.command_runs P.machine Q.machine P.seed P.clock Q.seed Q.clock
        (ConcatenationGenerator.concatSeed P.seed Q.seed) index _
        (ConcatenationGenerator.budgetConditions P.seed P.clock Q.seed Q.clock (ConcatenationGenerator.concatSeed P.seed Q.seed) index) tape
      exact ⟨t, result, run, output⟩)
    (ConcatenationGenerator.command_time P.machine Q.machine P.seed P.clock Q.seed Q.clock (ConcatenationGenerator.concatSeed P.seed Q.seed))
    n bits length.le
  simpa only [concatMachine, concatClock, ConcatenationGenerator.commandValue, ← length, le_refl, ite_true, List.take_length] using actual

noncomputable def concatenate : BoundedPhaseFamily α where
  machine := concatMachine P Q
  seed := ConcatenationGenerator.concatSeed P.seed Q.seed
  clock := concatClock P Q
  reciprocal := P.reciprocal.mul Q.reciprocal
  mean := by
    intro n
    unfold OptionPhase.HasMean OptionPhase.success
    simp_rw [concatMachine_value P Q n (List.ofFn _) List.length_ofFn]
    exact ConcatenationGenerator.algorithm_mean_full_seed P.machine Q.machine P.seed P.clock Q.seed Q.clock n
      (fun j _ => P.mean j) (fun j _ => Q.mean j)
  mass := by
    intro n active
    simp_rw [concatMachine_value P Q n (List.ofFn _) List.length_ofFn] at active ⊢
    obtain ⟨bits, word, output⟩ := active
    have positive : 0 < fairBlockMeasure (ConcatenationGenerator.concatSeed P.seed Q.seed n)
        {bits | ConcatenationGenerator.algorithm P.machine Q.machine P.seed P.clock Q.seed Q.clock n (List.ofFn bits) = some word} :=
      (fairBlockMeasure_event_pos_iff _ _).mpr ⟨bits, output⟩
    obtain ⟨j, within, left, right, leftMember, rightMember, _⟩ :=
      (ConcatenationGenerator.algorithm_word_probability P.machine Q.machine P.seed P.clock Q.seed Q.clock n _
        (ConcatenationGenerator.scanPhase_width_le P.machine Q.machine P.seed P.clock Q.seed Q.clock n) word).mp positive
    change left ∈ P.layer j at leftMember
    change right ∈ Q.layer (n-j) at rightMember
    obtain ⟨leftBits, leftOutput⟩ := (P.layer_iff j left).mp leftMember
    obtain ⟨rightBits, rightOutput⟩ := (Q.layer_iff (n-j) right).mp rightMember
    have leftMass := P.mass j ⟨leftBits, left, leftOutput⟩
    have rightMass := Q.mass (n-j) ⟨rightBits, right, rightOutput⟩
    have leftInverse : (P.reciprocal n : ℝ≥0∞)⁻¹ ≤ (P.reciprocal j : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (P.reciprocal.monotone within))
    have rightInverse : (Q.reciprocal n : ℝ≥0∞)⁻¹ ≤ (Q.reciprocal (n-j) : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Q.reciprocal.monotone (Nat.sub_le n j)))
    calc
      ((P.reciprocal.mul Q.reciprocal) n : ℝ≥0∞)⁻¹ = (P.reciprocal n : ℝ≥0∞)⁻¹ * (Q.reciprocal n : ℝ≥0∞)⁻¹ := by
        rw [PolynomialBound.mul_eval, Nat.cast_mul, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
      _ ≤ (P.reciprocal j : ℝ≥0∞)⁻¹ * (Q.reciprocal (n-j) : ℝ≥0∞)⁻¹ := mul_le_mul' leftInverse rightInverse
      _ ≤ (ConcatenationGenerator.sourcePhase P.machine P.seed P.clock j).successMass *
          (ConcatenationGenerator.sourcePhase Q.machine Q.seed Q.clock (n-j)).successMass := mul_le_mul' leftMass rightMass
      _ ≤ _ := ConcatenationGenerator.algorithm_success_ge_split_full_seed P.machine Q.machine P.seed P.clock Q.seed Q.clock n j within

theorem concatenate_layer_iff (n : ℕ) (word : List α) : word ∈ (P.concatenate Q).layer n ↔
    ∃ j ≤ n, ∃ left right, left ∈ P.layer j ∧ right ∈ Q.layer (n-j) ∧ left ++ right = word := by
  change (0 < fairBlockMeasure (ConcatenationGenerator.concatSeed P.seed Q.seed n)
    {bits | UnionGenerator.sourceValue (concatMachine P Q) (concatClock P Q) n (List.ofFn bits) = some word}) ↔ _
  simp_rw [concatMachine_value P Q n (List.ofFn _) List.length_ofFn]
  exact ConcatenationGenerator.algorithm_word_probability P.machine Q.machine P.seed P.clock Q.seed Q.clock n _
    (ConcatenationGenerator.scanPhase_width_le P.machine Q.machine P.seed P.clock Q.seed Q.clock n) word

theorem concatenate_layer (n : ℕ) : (P.concatenate Q).layer n = IndexedSupport.concatLayers P.layer Q.layer n := by
  ext word
  rw [concatenate_layer_iff]
  constructor
  · rintro ⟨j, within, left, right, leftMember, rightMember, equal⟩
    exact ⟨j, n-j, by omega, left, leftMember, right, rightMember, equal⟩
  · rintro ⟨i, j, sum, left, leftMember, right, rightMember, equal⟩
    exact ⟨i, by omega, left, right, leftMember, by simpa only [show n-i = j by omega] using rightMember, equal⟩

end
end ComplexityOfGenerators.BoundedPhaseFamily
