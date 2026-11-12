import ComplexityOfGenerators.Proofs.SelectedOriginalSampling.Basic

namespace ComplexityOfGenerators.SelectedOriginalSampling
open MeasureTheory
open scoped ENNReal
open OriginalSourceFamilySampler (Request)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α) (width : PolynomialBound)
    (value : ℕ → BitString → Option (List Request))
    (sound : ∀ n bits requests,value n bits=some requests →
      ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty)

theorem outer_tail (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) (stream : BitStream) :
    ((outer width value n positive).run stream).2=
      fun i => stream ((((outer width value n positive).run stream).1.1+1)*width n+i) := rfl

theorem outer_block (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) (stream : BitStream) :
    ((outer width value n positive).run stream).1.2=
      fixedBlock (width n) stream ((outer width value n positive).run stream).1.1 := rfl

theorem outer_failed (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n))
    (stream : BitStream) (k : ℕ) (earlier : k<((outer width value n positive).run stream).1.1) :
    value n (List.ofFn (fixedBlock (width n) stream k))=none := by
  have absent : fixedBlock (width n) stream k∉success width value n := by
    rcases firstSuccessIndex_spec (width n) (success width value n) stream with ⟨_,first⟩|⟨_,never⟩
    · exact first k earlier
    · exact never k
  cases found : value n (List.ofFn (fixedBlock (width n) stream k)) with
  | none => rfl
  | some requests => exact False.elim (absent (by simp [success,found]))

theorem draw_trace_ae (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) :
    ∀ᵐ stream∂fairCoinMeasure,
      let outcome := ((draw families width value sound n positive).run stream).1
      (∀ k<outcome.1.1,value n (List.ofFn (fixedBlock (width n) stream k))=none) ∧
      value n (List.ofFn (fixedBlock (width n) stream outcome.1.1))=some (selected width value n outcome.1) ∧
      OriginalSourceFamilySampler.StreamTrace families
        (fun i => stream (outerOffset width outcome+i)) (selected width value n outcome.1) outcome.2 := by
  let retry := outer width value n positive
  have traces : ∀ᵐ future∂fairCoinMeasure,∀ record : OuterRecord width n,
      OriginalSourceFamilySampler.StreamTrace families future (selected width value n record)
        ((OriginalSourceFamilySampler.calls families (selected width value n record)
          (selected_active families width value sound n record)).run future).1 := by
    apply ae_all_iff.mpr
    intro record
    exact OriginalSourceFamilySampler.calls_trace_ae families _ _
  have fresh := retry.tail_ae traces
  filter_upwards [outer_success_ae width value n positive,fresh] with stream accepted allTraces
  let record := (retry.run stream).1
  let records := ((OriginalSourceFamilySampler.calls families (selected width value n record)
    (selected_active families width value sound n record)).run (retry.run stream).2).1
  change (∀ k<record.1,value n (List.ofFn (fixedBlock (width n) stream k))=none) ∧
    value n (List.ofFn (fixedBlock (width n) stream record.1))=some (selected width value n record) ∧
    OriginalSourceFamilySampler.StreamTrace families
      (fun i => stream ((record.1+1)*width n+i)) (selected width value n record) records
  refine ⟨outer_failed width value n positive stream,?_,?_⟩
  · have equal : record.2=fixedBlock (width n) stream record.1 := rfl
    rw [← equal]
    change value n (List.ofFn record.2)=some ((value n (List.ofFn record.2)).getD [])
    change (value n (List.ofFn record.2)).isSome=true at accepted
    cases found : value n (List.ofFn record.2) with
    | none => simp only [found,Option.isSome_none,Bool.false_eq_true] at accepted
    | some requests => rfl
  · exact allTraces record

theorem draw_tail (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) (stream : BitStream) :
    ((draw families width value sound n positive).run stream).2=
      fun i => stream (outerOffset width (((draw families width value sound n positive).run stream).1)+
        sourceCoins width (((draw families width value sound n positive).run stream).1)+i) := by
  unfold draw
  simp only [FreshStreamSampler.bind,FreshStreamSampler.map]
  rw [OriginalSourceFamilySampler.calls_tail]
  simp only [outer_tail,outerOffset,sourceCoins,Nat.add_assoc]

theorem draw_native_prefix_ae (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) :
    ∀ᵐ stream∂fairCoinMeasure,
      let outcome := ((draw families width value sound n positive).run stream).1
      OriginalSourceFamilySampler.FiniteSequenceTrace families
        (streamPrefix stream (outerOffset width outcome+sourceCoins width outcome)) (outerOffset width outcome)
        (selected width value n outcome.1) outcome.2 := by
  filter_upwards [draw_trace_ae families width value sound n positive] with stream trace
  exact trace.2.2.native_prefix families stream _ _ _ _ le_rfl

end
end ComplexityOfGenerators.SelectedOriginalSampling
