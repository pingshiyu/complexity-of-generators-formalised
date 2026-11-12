import ComplexityOfGenerators.Proofs.ExpectedStarMoments
import ComplexityOfGenerators.Simulation.CertifiedStarPhase

/-! A concrete fair-stream execution of outer path retries followed by fresh
word calls. The conditional source samplers use the selected positive indices;
all means and cost moments refer to this same sequence of random bits. -/
namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

abbrev OuterRecord (p : PolynomialBound) (n : ℕ) := ℕ × (Fin (StarCertification.width p n) → Bool)

def successSet (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) :
    Set (Fin (StarCertification.width p n) → Bool) :=
  {bits | (CertifiedStarPhase.value G.machine p n (List.ofFn bits)).isSome}

private def Witness (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) : Prop :=
  ∃ parts, CertifiedStarPhase.AvailableComposition G n parts ∧
    CertifiedStarPhase.value G.machine p n bits = some (StarPaths.payload parts)

noncomputable def chosenParts (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) : List ℕ :=
  by
    classical
    exact if possible : Witness G p n bits then Classical.choose possible else []

private theorem witness_of_success (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (success : (CertifiedStarPhase.value G.machine p n bits).isSome = true) : Witness G p n bits := by
  obtain ⟨word,result⟩ := Option.isSome_iff_exists.mp success
  obtain ⟨parts,available,equal⟩ := CertifiedStarPhase.value_source_sound G p n bits word result
  exact ⟨parts,available,by simpa only [equal] using result⟩

theorem chosenParts_spec (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (success : (CertifiedStarPhase.value G.machine p n bits).isSome = true) :
    CertifiedStarPhase.AvailableComposition G n (chosenParts G p n bits) ∧
      CertifiedStarPhase.value G.machine p n bits = some (StarPaths.payload (chosenParts G p n bits)) := by
  have witnessed := witness_of_success G p n bits success
  simpa only [chosenParts,dite_eq_left witnessed] using Classical.choose_spec witnessed

theorem chosenParts_active (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∀ j ∈ chosenParts G p n bits, (G.layer j).Nonempty := by
  by_cases possible : Witness G p n bits
  · intro j member
    have spec := Classical.choose_spec possible
    simp only [chosenParts,dif_pos possible] at member
    exact (spec.1.2 j member).2
  · simp [chosenParts,possible]

private theorem positive_length_le_sum (parts : List ℕ) (positive : ∀ j ∈ parts, 0 < j) : parts.length ≤ parts.sum := by
  induction parts with
  | nil => simp
  | cons j parts ih =>
    have first := positive j (by simp)
    have tail := ih (fun k member => positive k (by simp [member]))
    simp only [List.length_cons,List.sum_cons]
    omega

private theorem member_le_sum (parts : List ℕ) (j : ℕ) (member : j ∈ parts) : j ≤ parts.sum := by
  induction parts with
  | nil => simp at member
  | cons k parts ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.sum_cons]; omega
    · have := ih member
      simp only [List.sum_cons]
      omega

theorem chosenParts_bounds (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    (chosenParts G p n bits).length ≤ n ∧ ∀ j ∈ chosenParts G p n bits, j ≤ n := by
  by_cases possible : Witness G p n bits
  · have spec := (Classical.choose_spec possible).1
    simp only [chosenParts,dif_pos possible]
    exact ⟨(positive_length_le_sum _ (fun j member => (spec.2 j member).1)).trans_eq spec.1,
      fun j member => (member_le_sum _ j member).trans_eq spec.1⟩
  · simp [chosenParts,possible]

variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))

def Available (n : ℕ) : Prop := ∃ parts, CertifiedStarPhase.AvailableComposition G n parts

include expected in
theorem success_mass (n : ℕ) (available : Available G n) :
    (1 : ℝ≥0∞)/2 ≤ fairBlockMeasure (StarCertification.width p n) (successSet G p n) := by
  obtain ⟨parts,productive⟩ := available
  have lower := CertifiedStarPhase.value_mass G p n parts productive expected
  have constant : (1 : ℝ≥0∞)/2 ≤ (1 : ℝ≥0∞)-1/8 := by
    have half : (1 : ℝ≥0∞)-1/2 = (1 : ℝ≥0∞)/2 := ENNReal.sub_half (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    calc
      (1 : ℝ≥0∞)/2 = 1-1/2 := half.symm
      _ ≤ _ := tsub_le_tsub_left (by
        simpa only [one_div] using ENNReal.inv_le_inv.mpr (by norm_num : (2 : ℝ≥0∞) ≤ 8)) 1
  exact constant.trans lower

include expected in
noncomputable def outerCall (n : ℕ) (available : Available G n) : FreshStreamSampler (OuterRecord p n) :=
  FreshStreamSampler.retry (StarCertification.width p n) ((StarCertification.width p).positive n)
    (successSet G p n) (Set.to_countable _ |>.measurableSet)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1/2) (success_mass G p expected n available))

variable (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

include layers in
theorem chosenParts_sourceActive (n : ℕ) (record : OuterRecord p n) :
    ∀ j ∈ chosenParts G p n (List.ofFn record.2), (P.layer j).Nonempty := by
  intro j member
  rw [layers]
  exact chosenParts_active G p n (List.ofFn record.2) j member

noncomputable def draw (n : ℕ) (available : Available G n) :
    FreshStreamSampler (OuterRecord p n × List (ℕ × List α)) :=
  (outerCall G p expected n available).bind (fun record =>
    (P.recordCalls (chosenParts G p n (List.ofFn record.2)) (chosenParts_sourceActive G p P layers n record)).map
      (fun records => (record,records)) (measurable_of_countable _))

end
end ComplexityOfGenerators.ExpectedStarSampling
