import ComplexityOfGenerators.Proofs.OriginalCertification.Basic

/-! Every split is tested once. Fair offers retain full support of the
productive splits and never discard the existence of a successful candidate. -/
namespace ComplexityOfGenerators.OriginalCertification.Concatenation
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α) (p : PolynomialBound)

def candidate (n j : ℕ) : FiniteBlockPhase Unit :=
  marker (FiniteBlockPhase.concatenate (source (families false).machine p j)
    (source (families true).machine p (n-j))) (List.replicate j ())
def phase (n : ℕ) : FiniteBlockPhase Unit :=
  FiniteBlockPhase.scan ((List.range (n+1)).map (candidate families p n))
def width : PolynomialBound :=
  ⟨9*p.coefficient,p.degree+1,Nat.mul_pos (by decide) p.coefficient_pos⟩
@[simp] theorem width_eval (n : ℕ) : width p n=9*(n+1)*p n := by
  simp only [width,PolynomialBound.eval,pow_succ]
  ring

private theorem width_list_bound (n : ℕ) (indices : List ℕ)
    (bounded : ∀ j∈indices,j≤n) :
    (indices.map (fun j => seed p j+seed p (n-j)+1)).sum ≤ indices.length*(9*p n) := by
  induction indices with
  | nil => simp
  | cons j indices ih =>
      have first : p j≤p n := Nat.mul_le_mul_left p.coefficient
        (pow_le_pow_left' (Nat.add_le_add_right (bounded j (by simp)) 1) p.degree)
      have second : p (n-j)≤p n := Nat.mul_le_mul_left p.coefficient
        (pow_le_pow_left' (Nat.add_le_add_right (Nat.sub_le n j) 1) p.degree)
      have positive := p.positive n
      have rest := ih (fun k member => bounded k (by simp [member]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,seed_eval]
      simp only [seed_eval] at rest
      nlinarith

theorem width_fits (n : ℕ) : (phase families p n).width≤width p n := by
  rw [phase,FiniteBlockPhase.scan_width]
  simp only [List.map_map]
  change ((List.range (n+1)).map (fun j => seed p j+seed p (n-j)+1)).sum≤width p n
  have bound := width_list_bound p n (List.range (n+1)) (by
    intro j member
    have := List.mem_range.mp member
    omega)
  rw [List.length_range] at bound
  simpa only [width_eval,Nat.mul_assoc,Nat.mul_left_comm] using bound

def value (n : ℕ) (bits : BitString) : Option (List Unit) := (phase families p n).evaluate bits
def choice (n : ℕ) (bits : BitString) : Option ℕ := (value families p n bits).map List.length
def Available (n : ℕ) : Prop :=
  ∃ j≤n,((families false).layer j).Nonempty ∧ ((families true).layer (n-j)).Nonempty

variable (expected : ∀ tag j,((families tag).layer j).Nonempty →
  (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
include expected

theorem candidate_language (n j : ℕ) (word : List Unit) :
    word∈(candidate families p n j).language ↔ word=List.replicate j () ∧
      ((families false).layer j).Nonempty ∧ ((families true).layer (n-j)).Nonempty := by
  rw [candidate,marker_language,FiniteBlockPhase.concatenate_success]
  have left := source_positive_iff (families false) p j (expected false j)
  have right := source_positive_iff (families true) p (n-j) (expected true (n-j))
  simp only [ENNReal.mul_pos_iff,left,right,and_assoc]

theorem phase_language (n : ℕ) (word : List Unit) :
    word∈(phase families p n).language ↔ ∃ j≤n,word=List.replicate j () ∧
      ((families false).layer j).Nonempty ∧ ((families true).layer (n-j)).Nonempty := by
  rw [phase,FiniteBlockPhase.scan_language]
  constructor
  · rintro ⟨part,member,supported⟩
    obtain ⟨j,within,equal⟩ :=
      (List.mem_map (f := candidate families p n) (l := List.range (n+1))).mp member
    subst part
    have bound := List.mem_range.mp within
    exact ⟨j,by omega,(candidate_language families p expected n j word).mp supported⟩
  · rintro ⟨j,within,valid⟩
    refine ⟨candidate families p n j,List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩,?_⟩
    exact (candidate_language families p expected n j word).mpr valid

theorem value_sound (n : ℕ) (bits : BitString) {word : List Unit}
    (result : value families p n bits=some word) :
    ∃ j≤n,word=List.replicate j () ∧ ((families false).layer j).Nonempty ∧
      ((families true).layer (n-j)).Nonempty := by
  apply (phase_language families p expected n word).mp
  have enough : (phase families p n).width≤bits.length := by
    by_contra absent
    simp only [value,FiniteBlockPhase.evaluate,dite_eq_right absent] at result
    cases result
  change 0<fairBlockMeasure (phase families p n).width {block | (phase families p n).value block=some word}
  apply (fairBlockMeasure_event_pos_iff _ _).mpr
  exact ⟨FiniteBlockPhase.sample bits _ enough,by
    simpa only [Set.mem_ofPred_eq,value,FiniteBlockPhase.evaluate_eq _ _ enough] using result⟩

theorem choice_sound (n : ℕ) (bits : BitString) {j : ℕ}
    (result : choice families p n bits=some j) :
    j≤n ∧ ((families false).layer j).Nonempty ∧ ((families true).layer (n-j)).Nonempty := by
  obtain ⟨word,produced,length⟩ := Option.map_eq_some_iff.mp result
  obtain ⟨k,within,equal,active⟩ := value_sound families p expected n bits produced
  have same : k=j := by simpa only [equal,List.length_replicate] using length
  exact same ▸ ⟨within,active⟩

theorem phase_mass (n : ℕ) (available : Available families n) :
    (1 : ℝ≥0∞)/4≤(phase families p n).successMass := by
  obtain ⟨j,within,left,right⟩ := available
  have leftMass := source_mass (families false).machine p j (expected false j left)
  have rightMass := source_mass (families true).machine p (n-j) (expected true (n-j) right)
  calc
    (1 : ℝ≥0∞)/4 = (1/2)*(1/2) := by
      simp only [one_div]
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    _ ≤ (source (families false).machine p j).successMass*(source (families true).machine p (n-j)).successMass :=
      mul_le_mul' leftMass rightMass
    _ = (candidate families p n j).successMass := by
      rw [candidate,marker_success,FiniteBlockPhase.concatenate_success]
    _ ≤ _ := FiniteBlockPhase.scan_success_ge_member _ (candidate families p n j)
      (List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩)

theorem choice_mass (n : ℕ) (available : Available families n) :
    (1 : ℝ≥0∞)/4≤fairBlockMeasure (width p n) {bits | (choice families p n (List.ofFn bits)).isSome} := by
  have law := FiniteBlockPhase.evaluate_event_measure (phase families p n) (width p n) (width_fits families p n)
    (fun output => output.isSome=true)
  have same : {bits : Fin (width p n) → Bool | (choice families p n (List.ofFn bits)).isSome}=
      {bits | ((phase families p n).evaluate (List.ofFn bits)).isSome} := by
    ext bits
    simp [choice,value]
  rw [same,law]
  exact phase_mass families p expected n available

theorem choice_support (n j : ℕ) :
    (0<fairBlockMeasure (width p n) {bits | choice families p n (List.ofFn bits)=some j}) ↔
      j≤n ∧ ((families false).layer j).Nonempty ∧ ((families true).layer (n-j)).Nonempty := by
  constructor
  · intro positive
    obtain ⟨bits,result⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
    exact choice_sound families p expected n (List.ofFn bits) result
  · rintro ⟨within,left,right⟩
    have supported := (phase_language families p expected n (List.replicate j ())).mpr ⟨j,within,rfl,left,right⟩
    have law := FiniteBlockPhase.evaluate_event_measure (phase families p n) (width p n) (width_fits families p n)
      (fun output => output=some (List.replicate j ()))
    have positive : 0<fairBlockMeasure (width p n) {bits | value families p n (List.ofFn bits)=some (List.replicate j ())} := by
      change 0<fairBlockMeasure (width p n) {bits | (phase families p n).evaluate (List.ofFn bits)=some (List.replicate j ())}
      rw [law]
      exact supported
    obtain ⟨bits,result⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
    change value families p n (List.ofFn bits)=some (List.replicate j ()) at result
    apply (fairBlockMeasure_event_pos_iff _ _).mpr
    refine ⟨bits,?_⟩
    change choice families p n (List.ofFn bits)=some j
    simp only [choice,result,Option.map_some,List.length_replicate]

end
end ComplexityOfGenerators.OriginalCertification.Concatenation
