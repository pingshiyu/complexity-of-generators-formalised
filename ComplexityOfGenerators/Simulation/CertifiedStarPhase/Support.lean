import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Phase
import ComplexityOfGenerators.Proofs.StarCertificationProbability

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open MeasureTheory
open scoped ENNReal
variable {α : Type} [Fintype α]
set_option backward.isDefEq.respectTransparency true

/-- A productive decomposition is indexed by positive source indices. The
indices concern expected source lengths; the eventual factor words need not
have those lengths on every run. -/
def AvailableComposition (G : UniformGenerators α) (n : ℕ) (parts : StarPaths.Parts) : Prop :=
  parts.sum = n ∧ ∀ j ∈ parts, 0 < j ∧ (G.layer j).Nonempty

private theorem part_le_sum (parts : List ℕ) (j : ℕ) (member : j ∈ parts) : j ≤ parts.sum := by
  induction parts with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.sum_cons]
        omega
      · have bound := ih member
        simp only [List.sum_cons]
        omega

theorem value_source_sound (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (word : List StarPaths.Symbol) (result : value G.machine p n bits = some word) :
    ∃ parts, AvailableComposition G n parts ∧ word = StarPaths.payload parts := by
  obtain ⟨parts,valid,equal⟩ := value_sound G.machine p n bits word result
  refine ⟨parts,⟨valid.1,?_⟩,equal⟩
  intro j member
  have positive := (valid.2 j member).1
  have inside : j ≤ n := (part_le_sum parts j member).trans_eq valid.1
  have active := StarCertification.walk_sound G p 0 n bits j positive inside (valid.2 j member).2
  exact ⟨positive,by simpa using active⟩

/-- Recognising all productive indices makes the path selector succeed for
every remaining cut word, without a conditional rejection bias. -/
theorem value_of_allActive (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (parts : StarPaths.Parts) (available : AvailableComposition G n parts)
    (certified : StarCertification.allActiveCertified G p n bits) :
    (value G.machine p n bits).isSome = true := by
  apply (value_isSome G.machine p n bits).mpr
  refine ⟨parts,available.1,?_⟩
  intro j member
  have positive := (available.2 j member).1
  have inside : j ≤ n := (part_le_sum parts j member).trans_eq available.1
  let index : Fin n := ⟨j-1,by omega⟩
  have same : (index : ℕ)+1 = j := by dsimp only [index]; omega
  have active : (G.layer ((index : ℕ)+1)).Nonempty := by rw [same]; exact (available.2 j member).2
  exact ⟨positive,certified index active⟩

/-- Constant success mass for the concrete bounded outer path-selection
phase, derived only from the original source's expected runtime bounds. -/
theorem value_mass (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ)
    (parts : StarPaths.Parts) (available : AvailableComposition G n parts)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞)) :
    (1 : ℝ≥0∞)-(1 : ℝ≥0∞)/8 ≤ fairBlockMeasure (StarCertification.width p n)
      {bits | (value G.machine p n (List.ofFn bits)).isSome} := by
  have bound := StarCertification.allActiveCertified_mass G p n expected
  apply bound.trans
  apply measure_mono
  intro bits certified
  exact value_of_allActive G p n (List.ofFn bits) parts available certified

end ComplexityOfGenerators.Simulation.CertifiedStarPhase
