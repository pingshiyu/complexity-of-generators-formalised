import ComplexityOfGenerators.Foundations.FreshStreamSequence
import ComplexityOfGenerators.Foundations.CountableLists

namespace ComplexityOfGenerators.FreshStreamSampler
open MeasureTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]

noncomputable def sequenceList (samplers : List (FreshStreamSampler A)) : FreshStreamSampler (List A) :=
  (sequence samplers).map List.ofFn (measurable_of_countable _)

@[simp] theorem sequenceList_nil (stream : BitStream) :
    (sequenceList ([] : List (FreshStreamSampler A))).run stream = ([],stream) := rfl

/-- The list view exposes the actual sequential execution of the finite
vector sampler, without changing which bits each call consumes. -/
theorem sequenceList_cons (sampler : FreshStreamSampler A) (rest : List (FreshStreamSampler A))
    (stream : BitStream) :
    (sequenceList (sampler::rest)).run stream =
      (let first := sampler.run stream
       let remaining := (sequenceList rest).run first.2
       (first.1::remaining.1,remaining.2)) := by
  apply Prod.ext
  · simp [sequenceList,sequence,map,bind,List.ofFn_succ]
  · rfl

theorem sequenceList_length (samplers : List (FreshStreamSampler A)) (stream : BitStream) :
    ((sequenceList samplers).run stream).1.length = samplers.length := by
  simp [sequenceList,map]

end
end ComplexityOfGenerators.FreshStreamSampler
