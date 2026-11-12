import ComplexityOfGenerators.Proofs.BoundedPhaseFamilies
import ComplexityOfGenerators.Proofs.BoundedCommandPhase
import ComplexityOfGenerators.Simulation.UnionGenerator.Execution
import ComplexityOfGenerators.Simulation.UnionGenerator.PhaseMeans

/-! A native bounded phase for union, preserving exact phase means and full
support. One shared retry constructor supplies the expected-time family. -/
namespace ComplexityOfGenerators.BoundedPhaseFamily
open Simulation WordStack MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (P Q : BoundedPhaseFamily α)

def unionCode := UnionGenerator.command P.machine Q.machine P.seed P.clock Q.seed Q.clock
  (UnionGenerator.unionSeed P.seed Q.seed)

noncomputable def unionMachine := ((unionCode P Q).program 0).machine
noncomputable def unionClock := Program.compiledTime
  (UnionGenerator.stackTime P.machine Q.machine P.seed P.clock Q.seed Q.clock (UnionGenerator.unionSeed P.seed Q.seed))

theorem unionMachine_value (n : ℕ) (bits : BitString) (length : bits.length = UnionGenerator.unionSeed P.seed Q.seed n) :
    UnionGenerator.sourceValue (unionMachine P Q) (unionClock P Q) n bits =
      UnionGenerator.value P.machine Q.machine P.seed P.clock Q.seed Q.clock n bits := by
  have actual := Command.bounded_sourceValue (unionCode P Q) 0 (UnionGenerator.unionSeed P.seed Q.seed)
    (UnionGenerator.stackTime P.machine Q.machine P.seed P.clock Q.seed Q.clock (UnionGenerator.unionSeed P.seed Q.seed))
    (UnionGenerator.commandValue P.machine Q.machine P.seed P.clock Q.seed Q.clock (UnionGenerator.unionSeed P.seed Q.seed))
    (by
      intro index tape
      obtain ⟨t, _, result, run, output⟩ := UnionGenerator.command_runs P.machine Q.machine P.seed P.clock Q.seed Q.clock
        (UnionGenerator.unionSeed P.seed Q.seed) index _
        (UnionGenerator.budgetConditions P.seed P.clock Q.seed Q.clock (UnionGenerator.unionSeed P.seed Q.seed) index) tape
      exact ⟨t, result, run, output⟩)
    (UnionGenerator.command_time P.machine Q.machine P.seed P.clock Q.seed Q.clock (UnionGenerator.unionSeed P.seed Q.seed))
    n bits length.le
  simpa only [unionMachine, unionClock, UnionGenerator.commandValue, ← length, le_refl, ite_true, List.take_length] using actual

noncomputable def union : BoundedPhaseFamily α where
  machine := unionMachine P Q
  seed := UnionGenerator.unionSeed P.seed Q.seed
  clock := unionClock P Q
  reciprocal := P.reciprocal.add Q.reciprocal
  mean := by
    intro n
    unfold OptionPhase.HasMean OptionPhase.success
    simp_rw [unionMachine_value P Q n (List.ofFn _) List.length_ofFn]
    exact UnionGenerator.value_mean_full_seed P.machine Q.machine P.seed P.clock Q.seed Q.clock n (P.mean n) (Q.mean n)
  mass := by
    intro n active
    simp_rw [unionMachine_value P Q n (List.ofFn _) List.length_ofFn] at active ⊢
    obtain ⟨bits, word, output⟩ := active
    have positive : 0 < fairBlockMeasure (UnionGenerator.unionSeed P.seed Q.seed n)
        {bits | UnionGenerator.value P.machine Q.machine P.seed P.clock Q.seed Q.clock n (List.ofFn bits) = some word} :=
      (fairBlockMeasure_event_pos_iff _ _).mpr ⟨bits, output⟩
    have supported := (UnionGenerator.value_word_probability P.machine Q.machine P.seed P.clock Q.seed Q.clock n _
      (UnionGenerator.offerPhase_width_le P.machine Q.machine P.seed P.clock Q.seed Q.clock n) word).mp positive
    have sum := P.reciprocal.add_le Q.reciprocal n
    rcases supported with left | right
    · change word ∈ P.layer n at left
      obtain ⟨source, produces⟩ := (P.layer_iff n word).mp left
      calc
        ((P.reciprocal.add Q.reciprocal) n : ℝ≥0∞)⁻¹ ≤ (P.reciprocal n : ℝ≥0∞)⁻¹ :=
          ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (by omega))
        _ ≤ (UnionGenerator.sourcePhase P.machine P.seed P.clock n).successMass := P.mass n ⟨source, word, produces⟩
        _ ≤ _ := UnionGenerator.value_success_ge_left P.machine Q.machine P.seed P.clock Q.seed Q.clock n _
          (UnionGenerator.offerPhase_width_le P.machine Q.machine P.seed P.clock Q.seed Q.clock n)
    · change word ∈ Q.layer n at right
      obtain ⟨source, produces⟩ := (Q.layer_iff n word).mp right
      calc
        ((P.reciprocal.add Q.reciprocal) n : ℝ≥0∞)⁻¹ ≤ (Q.reciprocal n : ℝ≥0∞)⁻¹ :=
          ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (by omega))
        _ ≤ (UnionGenerator.sourcePhase Q.machine Q.seed Q.clock n).successMass := Q.mass n ⟨source, word, produces⟩
        _ ≤ _ := UnionGenerator.value_success_ge_right P.machine Q.machine P.seed P.clock Q.seed Q.clock n _
          (UnionGenerator.offerPhase_width_le P.machine Q.machine P.seed P.clock Q.seed Q.clock n)

theorem union_layer (n : ℕ) : (P.union Q).layer n = P.layer n ∪ Q.layer n := by
  ext word
  change (0 < fairBlockMeasure (UnionGenerator.unionSeed P.seed Q.seed n)
    {bits | UnionGenerator.sourceValue (unionMachine P Q) (unionClock P Q) n (List.ofFn bits) = some word}) ↔ _
  simp_rw [unionMachine_value P Q n (List.ofFn _) List.length_ofFn]
  exact UnionGenerator.value_word_probability P.machine Q.machine P.seed P.clock Q.seed Q.clock n _
    (UnionGenerator.offerPhase_width_le P.machine Q.machine P.seed P.clock Q.seed Q.clock n) word

end
end ComplexityOfGenerators.BoundedPhaseFamily
