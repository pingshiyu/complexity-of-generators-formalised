import ComplexityOfGenerators.Proofs.OriginalSourceBinaryWitnesses
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses

/-! Global lucky binary witnesses retain actual minimal source prefixes. Their
producing indices and total native source time are polynomial in final word
length, with no per-layer short-path or supported-output cap premise. -/
namespace ComplexityOfGenerators.OriginalSourceClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

def binaryWork (q : PolynomialBound) : PolynomialBound := (⟨4,0,by decide⟩ : PolynomialBound).mul q

theorem union_fast_records (families : Bool → UniformGenerators α)
    (fast : ∀ tag,(families tag).GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ word∈(families false).language∪(families true).language,
      ∃ tag : Bool,∃ index : ℕ,∃ records : List OriginalSourceFamilySampler.Record,
        index≤q word.length ∧ ((families tag).layer index).Nonempty ∧
        records.map OriginalSourceFamilySampler.request=[(tag,index)] ∧
        (∀ record∈records,OriginalSourceFamilySampler.MinimalRecord families record) ∧
        OriginalSourceFamilySampler.words families records=word ∧
        OriginalSourceFamilySampler.totalTime families records+records.length≤binaryWork q word.length := by
  obtain ⟨q,paths⟩ := binary_bounded_witnesses families fast
  refine ⟨q,?_⟩
  intro word member
  have selected : ∃ tag,word∈(families tag).language := by
    rcases member with left|right
    · exact ⟨false,left⟩
    · exact ⟨true,right⟩
  obtain ⟨tag,member⟩ := selected
  obtain ⟨index,small,bits,nonempty,run⟩ := paths tag word member word.length le_rfl
  have active : ((families tag).layer index).Nonempty := ⟨word,bits,nonempty,q word.length,run⟩
  have sourcePaths : List.Forall₂ (OriginalSourceFamilySampler.WordPath families (q word.length)) [(tag,index)] [word] :=
    .cons ⟨bits,run⟩ .nil
  obtain ⟨records,labels,outputs,minimal,timeBound⟩ := OriginalSourceFamilySampler.bounded_records families (q word.length) _ _ sourcePaths
  have count : records.length=1 := by
    have sizes := congrArg List.length labels
    simpa only [List.length_map,List.length_singleton] using sizes
  have time : OriginalSourceFamilySampler.totalTime families records≤q word.length := by
    simpa only [List.length_singleton,Nat.one_mul] using timeBound
  refine ⟨tag,index,records,small,active,labels,minimal,?_,?_⟩
  · simpa using outputs
  · rw [binaryWork,PolynomialBound.mul_eval]
    change _≤4*(word.length+1)^0*q word.length
    rw [pow_zero,Nat.mul_one]
    have positive := q.positive word.length
    omega

theorem concat_fast_records (families : Bool → UniformGenerators α)
    (fast : ∀ tag,(families tag).GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ word∈IndexedSupport.concat (families false).language (families true).language,
      ∃ left right : ℕ,∃ records : List OriginalSourceFamilySampler.Record,
        left+right≤(q.add q) word.length ∧ ((families false).layer left).Nonempty ∧ ((families true).layer right).Nonempty ∧
        records.map OriginalSourceFamilySampler.request=[(false,left),(true,right)] ∧
        (∀ record∈records,OriginalSourceFamilySampler.MinimalRecord families record) ∧
        OriginalSourceFamilySampler.words families records=word ∧
        OriginalSourceFamilySampler.totalTime families records+records.length≤binaryWork q word.length := by
  obtain ⟨q,paths⟩ := concat_fast_witnesses families fast
  refine ⟨q,?_⟩
  intro word member
  obtain ⟨u,v,left,right,leftBits,rightBits,equal,small,leftNonempty,rightNonempty,leftRun,rightRun⟩ := paths word member
  have activeLeft : ((families false).layer left).Nonempty := ⟨u,leftBits,leftNonempty,q word.length,leftRun⟩
  have activeRight : ((families true).layer right).Nonempty := ⟨v,rightBits,rightNonempty,q word.length,rightRun⟩
  have sourcePaths : List.Forall₂ (OriginalSourceFamilySampler.WordPath families (q word.length))
      [(false,left),(true,right)] [u,v] := .cons ⟨leftBits,leftRun⟩ (.cons ⟨rightBits,rightRun⟩ .nil)
  obtain ⟨records,labels,outputs,minimal,timeBound⟩ := OriginalSourceFamilySampler.bounded_records families (q word.length) _ _ sourcePaths
  have count : records.length=2 := by
    have sizes := congrArg List.length labels
    simpa only [List.length_map,List.length_cons,List.length_nil] using sizes
  have time : OriginalSourceFamilySampler.totalTime families records≤2*q word.length := by
    simpa only [List.length_cons,List.length_nil] using timeBound
  refine ⟨left,right,records,small,activeLeft,activeRight,labels,minimal,?_,?_⟩
  · simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,equal] using outputs
  · rw [binaryWork,PolynomialBound.mul_eval]
    change _≤4*(word.length+1)^0*q word.length
    rw [pow_zero,Nat.mul_one]
    have positive := q.positive word.length
    omega

end
end ComplexityOfGenerators.OriginalSourceClosure
