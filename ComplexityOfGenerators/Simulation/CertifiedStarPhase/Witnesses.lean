import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Support
import ComplexityOfGenerators.Simulation.StarPaths.Padding

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open MeasureTheory
open scoped ENNReal
variable {α : Type} [Fintype α]
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
noncomputable section

/-- Once all assigned test blocks fit in a testPrefix, changing its unused suffix
cannot alter the cache. The supplied suffix remains fresh for path coins. -/
theorem walk_append (M : Machine Unit Bool α) (p : PolynomialBound) (start count : ℕ)
    (bits extra : BitString) (enough : StarCertification.used p start count ≤ bits.length) :
    StarCertification.walk M p start count (bits++extra) =
      ((StarCertification.walk M p start count bits).1,(StarCertification.walk M p start count bits).2++extra) := by
  induction count generalizing start bits with
  | zero => rfl
  | succ count ih =>
      have first : IndexwiseCertification.seed p (start+1) ≤ bits.length := by
        simp only [StarCertification.used] at enough
        omega
      have remaining : StarCertification.used p (start+1) count ≤ (bits.drop (IndexwiseCertification.seed p (start+1))).length := by
        simp only [StarCertification.used,List.length_drop] at enough ⊢
        omega
      have flag : StarCertification.testFlag M p (start+1) (bits++extra) = StarCertification.testFlag M p (start+1) bits := by
        unfold StarCertification.testFlag
        rw [List.take_append_of_le_length first]
      simp only [StarCertification.walk]
      rw [flag,List.drop_append_of_le_length first,ih (start+1) (bits.drop (IndexwiseCertification.seed p (start+1))) remaining]

theorem walk_exact_prefix (M : Machine Unit Bool α) (p : PolynomialBound) (start count : ℕ)
    (bits extra : BitString) (length : bits.length = StarCertification.used p start count) :
    StarCertification.walk M p start count (bits++extra) = ((StarCertification.walk M p start count bits).1,extra) := by
  have appended := walk_append M p start count bits extra (by omega)
  have empty : (StarCertification.walk M p start count bits).2 = [] := by
    rw [StarCertification.walk_remaining]
    exact List.drop_eq_nil_of_le (by omega)
  simpa only [empty,List.nil_append] using appended

private theorem part_le_sum (parts : List ℕ) (j : ℕ) (member : j ∈ parts) : j ≤ parts.sum := by
  induction parts with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.sum_cons]; omega
      · have := ih member; simp only [List.sum_cons]; omega

private theorem available_valid (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (parts : StarPaths.Parts) (available : AvailableComposition G n parts)
    (certified : StarCertification.allActiveCertified G p n bits) :
    StarPaths.Valid (StarCertification.walk G.machine p 0 n bits).1 n parts := by
  refine ⟨available.1,?_⟩
  intro j member
  have positive := (available.2 j member).1
  have inside : j ≤ n := (part_le_sum parts j member).trans_eq available.1
  let index : Fin n := ⟨j-1,by omega⟩
  have same : (index : ℕ)+1 = j := by dsimp only [index]; omega
  have active : (G.layer ((index : ℕ)+1)).Nonempty := by rw [same]; exact (available.2 j member).2
  exact ⟨positive,certified index active⟩

/-- Every productive composition has a concrete fixed-width phase witness.
Only the certification testPrefix is retained from the positive-mass event; the
unused suffix is replaced by the desired cut word and deterministic padding. -/
theorem value_full_support (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ)
    (parts : StarPaths.Parts) (available : AvailableComposition G n parts)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞)) :
    ∃ bits : BitString, bits.length = StarCertification.width p n ∧
      value G.machine p n bits = some (StarPaths.payload parts) := by
  have mass := StarCertification.allActiveCertified_mass G p n expected
  have positive : (0 : ℝ≥0∞) < (1 : ℝ≥0∞)-(1 : ℝ≥0∞)/8 := by norm_num
  obtain ⟨original,certified⟩ := nonempty_of_measure_ne_zero (positive.trans_le mass).ne'
  let source := List.ofFn original
  let used := StarCertification.used p 0 n
  let testPrefix := source.take used
  have sourceLength : source.length = StarCertification.width p n := by simp [source]
  have fits : used ≤ source.length := by
    have bound := StarCertification.used_bound p 0 n
    have width := StarCertification.width_lower p n
    simp only [Nat.zero_add] at bound
    dsimp only [used]
    rw [sourceLength]
    nlinarith
  have prefixLength : testPrefix.length = used := by simp [testPrefix,Nat.min_eq_left fits]
  have split : testPrefix++source.drop used = source := List.take_append_drop used source
  have stable : (StarCertification.walk G.machine p 0 n source).1 =
      (StarCertification.walk G.machine p 0 n testPrefix).1 := by
    rw [← split,walk_exact_prefix G.machine p 0 n testPrefix (source.drop used) prefixLength]
  have prefixCertified : StarCertification.allActiveCertified G p n testPrefix := by
    intro i active
    have accepted := certified i active
    change (((StarCertification.walk G.machine p 0 n testPrefix).1)[i.val]?).getD false = true
    rw [← stable]
    exact accepted
  have valid := available_valid G p n testPrefix parts available prefixCertified
  obtain ⟨cuts,cutsLength,selected⟩ := StarPaths.selected_full_support_padded
    (StarCertification.walk G.machine p 0 n testPrefix).1 n (StarCertification.width p n-used) parts
      (StarCertification.width_remaining p n) valid
  refine ⟨testPrefix++cuts,?_,?_⟩
  · simp only [List.length_append,prefixLength,cutsLength]
    rw [sourceLength] at fits
    omega
  · unfold value pathChoice
    rw [walk_exact_prefix G.machine p 0 n testPrefix cuts prefixLength]
    dsimp only
    rw [selected]
    rfl

end
end ComplexityOfGenerators.Simulation.CertifiedStarPhase
