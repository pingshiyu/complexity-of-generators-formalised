import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Basic
import ComplexityOfGenerators.Simulation.OriginalHeaderController.Execution

namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)

omit [Fintype α] in
/-- A selected split comes from the finite scan of `0,...,n`, regardless of
which source layers are productive. -/
theorem concat_choice_bounded (n : ℕ) (bits : BitString) {j : ℕ}
    (chosen : OriginalCertification.Concatenation.choice families p n bits=some j) : j≤n := by
  obtain ⟨word,produced,length⟩ := Option.map_eq_some_iff.mp chosen
  have enough : (OriginalCertification.Concatenation.phase families p n).width≤bits.length := by
    by_contra absent
    simp only [OriginalCertification.Concatenation.value,FiniteBlockPhase.evaluate,dite_eq_right absent] at produced
    cases produced
  have supported : word∈(OriginalCertification.Concatenation.phase families p n).language := by
    apply (fairBlockMeasure_event_pos_iff _ _).mpr
    refine ⟨FiniteBlockPhase.sample bits _ enough,?_⟩
    simpa only [Set.mem_ofPred_eq,OriginalCertification.Concatenation.value,
      FiniteBlockPhase.evaluate_eq _ _ enough] using produced
  rw [OriginalCertification.Concatenation.phase,FiniteBlockPhase.scan_language] at supported
  obtain ⟨phase,member,supported⟩ := supported
  obtain ⟨k,within,rfl⟩ := List.mem_map.mp member
  have wordShape := (OriginalCertification.marker_language _ _ word).mp supported |>.1
  have bound := List.mem_range.mp within
  have same : k=j := by simpa only [wordShape,List.length_replicate] using length
  omega

omit [Fintype α] in
theorem selection_choice (operation : Operation) (n : ℕ) (bits : BitString) (requests : List Request)
    (selected : selection families p operation n bits=some requests) :
    OriginalHeaderController.Choice operation n (headerOf operation n requests) requests := by
  cases operation with
  | union =>
      obtain ⟨tag,_,rfl⟩ := Option.map_eq_some_iff.mp selected
      exact ⟨tag,rfl,rfl⟩
  | concatenation =>
      obtain ⟨j,chosen,rfl⟩ := Option.map_eq_some_iff.mp selected
      exact ⟨j,concat_choice_bounded families p n bits chosen,rfl,rfl⟩

theorem reference_view (operation : Operation) (n : ℕ) (bits : BitString) (length : bits.length=width p operation n) :
    reference families p operation n bits=(selection families p operation n bits).map (headerOf operation n) := by
  cases operation with
  | union =>
      unfold reference OriginalHeaderController.reference selector selectorClock
      rw [OriginalBinarySelector.native_union_view families p n bits length]
      simp only [selection,ExpectedOriginalBinarySampling.selection,ExpectedOriginalUnionSampling.selection,Option.map_map]
      rfl
  | concatenation =>
      unfold reference OriginalHeaderController.reference selector selectorClock
      rw [OriginalBinarySelector.native_concat_view families p n bits length]
      simp only [selection,ExpectedOriginalBinarySampling.selection,ExpectedOriginalConcatenationSampling.selection,Option.map_map]
      rfl

theorem controller_shape (operation : Operation) (n : ℕ) :
    OriginalHeaderController.Shape (selector families p operation) (width p operation)
      (selectorClock families p operation) operation n := by
  intro block length header accepted
  change reference families p operation n block=some header at accepted
  rw [reference_view families p operation n block length] at accepted
  obtain ⟨requests,selected,equal⟩ := Option.map_eq_some_iff.mp accepted
  subst header
  exact ⟨requests,selection_choice families p operation n block requests selected⟩

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
