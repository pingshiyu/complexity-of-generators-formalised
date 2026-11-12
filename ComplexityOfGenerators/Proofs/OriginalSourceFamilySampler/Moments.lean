import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler.Sequence

/-! Additive original-source means need only first moments. No variance or
per-layer bound on supported outputs is imposed. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α)

theorem calls_sum_integral (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) (value : Record → ℝ≥0∞) :
    (∫⁻ stream, ((((calls families requests active).run stream).1).map value).sum∂fairCoinMeasure)=
      (requests.attach.map (fun entry =>
        ∫⁻ stream,value ((call families entry.1.1 entry.1.2 (active entry.1 entry.2)).run stream).1
          ∂fairCoinMeasure)).sum := by
  have additive := FreshStreamSampler.sequence_lintegral_sum (samplers families requests active) value
  simpa only [calls,FreshStreamSampler.sequenceList,FreshStreamSampler.map,List.map_ofFn,List.sum_ofFn,
    samplers,List.map_map,Function.comp_def] using additive

theorem words_length (records : List Record) :
    ((words families records).length : ℝ≥0∞)=
      (records.map (fun record => ((word families record).length : ℝ≥0∞))).sum := by
  induction records with
  | nil => simp [words]
  | cons record records ih =>
      simpa only [words,List.map_cons,List.flatten_cons,List.length_append,Nat.cast_add,
        List.sum_cons] using congrArg (fun value : ℝ≥0∞ => ((word families record).length : ℝ≥0∞)+value) ih

theorem time_sum (records : List Record) :
    (totalTime families records : ℝ≥0∞)=
      (records.map (fun record => (time families record : ℝ≥0∞))).sum := by
  induction records with
  | nil => simp [totalTime]
  | cons record records ih =>
      simpa only [totalTime,List.map_cons,List.sum_cons,Nat.cast_add] using
        congrArg (fun value : ℝ≥0∞ => (time families record : ℝ≥0∞)+value) ih

theorem calls_word_mean (mean : ∀ tag,(families tag).ExpectedLength)
    (requests : List Request) (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) :
    (∫⁻ stream,((words families ((calls families requests active).run stream).1).length : ℝ≥0∞)
      ∂fairCoinMeasure)=((requests.map Prod.snd).sum : ℝ≥0∞) := by
  simp_rw [words_length]
  rw [calls_sum_integral]
  simp_rw [call_mean families mean]
  calc
    _ = (requests.map (fun entry : Request => (entry.2 : ℝ≥0∞))).sum :=
      congrArg List.sum (List.attach_map_val (l := requests) (f := fun entry : Request => (entry.2 : ℝ≥0∞)))
    _ = _ := by simp [Function.comp_def]

theorem calls_runtime (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) :
    (∫⁻ stream,(totalTime families ((calls families requests active).run stream).1 : ℝ≥0∞)
      ∂fairCoinMeasure)=
      (requests.map (fun entry => (families entry.1).machine.expectedRuntime (generatorData entry.2))).sum := by
  simp_rw [time_sum]
  rw [calls_sum_integral]
  simp_rw [call_runtime]
  exact congrArg List.sum (List.attach_map_val (l := requests)
    (f := fun entry : Request => (families entry.1).machine.expectedRuntime (generatorData entry.2)))

theorem calls_runtime_le (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
    (requests : List Request) (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty)
    (target : ℕ) (indices : ∀ entry∈requests,entry.2≤target) :
    (∫⁻ stream,(totalTime families ((calls families requests active).run stream).1 : ℝ≥0∞)
      ∂fairCoinMeasure)≤(requests.length : ℝ≥0∞)*(p target : ℝ≥0∞) := by
  rw [calls_runtime]
  induction requests with
  | nil => simp
  | cons entry requests ih =>
      have first := expected entry.1 entry.2 (active entry (by simp))
      have monotone : p entry.2≤p target := Nat.mul_le_mul_left p.coefficient
        (pow_le_pow_left' (Nat.add_le_add_right (indices entry (by simp)) 1) p.degree)
      have firstBound := first.trans (Nat.cast_le.mpr monotone)
      have rest := ih (fun item member => active item (by simp [member]))
        (fun item member => indices item (by simp [member]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      exact (add_le_add firstBound rest).trans_eq (add_comm _ _)

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
