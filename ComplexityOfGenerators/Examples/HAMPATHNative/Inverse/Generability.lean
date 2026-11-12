import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.ValueControl
import ComplexityOfGenerators.Examples.InverseInputBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse

def seed : PolynomialBound := ⟨3,1,by omega⟩

@[simp] theorem seed_eq (n : ℕ) : seed n=3*(n+1) := by simp [seed,PolynomialBound.eval]

theorem inverseFibre_productive (n : ℕ) (target label word : List Symbol)
    (supported : word∈selfReduction.inverseFibre n target label) : BaseSearch.Productive n := by
  obtain ⟨_,source,⟨⟨graph,start,member,encoded⟩,length⟩,_⟩ :=
    selfReduction.mem_ancestors_iff.mp supported.1
  have positive : 1≤graph.size := by have := member.start_bound; omega
  have same : encodingLength graph.size=n := by rw [← encoded,Graph.encode_length] at length; exact length
  exact ⟨graph.size,by unfold encodingLength at same; omega,positive,same⟩

theorem value_complete_any (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label word : List Symbol) (supported : word∈selfReduction.inverseFibre n (graph.encode start) label) :
    ∃ bits, bits.length≤width (graph.size+1)+2*graph.size ∧ value graph start n label bits=some word := by
  obtain ⟨M,_,_,rfl⟩ := inverseFibre_productive n (graph.encode start) label word supported
  exact value_complete graph start M member label word supported

theorem seed_enough (graph : Graph) (start n : ℕ) (label word : List Symbol)
    (supported : word∈selfReduction.inverseFibre n (graph.encode start) label) :
    width (graph.size+1)+2*graph.size≤seed n := by
  have targetBound := (selfReduction.inverse_input_bounds word_rank_bound supported).1
  rw [Graph.encode_length] at targetBound
  have sizeBound : graph.size≤n := by unfold encodingLength at targetBound; omega
  have labelBound := width_le_size (graph.size+1)
  rw [seed_eq]
  omega

theorem value_complete_seed (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label word : List Symbol) (supported : word∈selfReduction.inverseFibre n (graph.encode start) label) :
    ∃ bits, bits.length=seed n ∧ value graph start n label bits=some word := by
  obtain ⟨original,short,produced⟩ := value_complete_any graph start n member label word supported
  have enoughSeed := seed_enough graph start n label word supported
  have sourceBound : original.length≤seed n := short.trans enoughSeed
  let bits := original++List.replicate (seed n-original.length) false
  have length : bits.length=seed n := by
    simp only [bits,List.length_append,List.length_replicate]
    omega
  refine ⟨bits,length,?_⟩
  by_cases empty : label=[]
  · simpa only [value,empty,List.nil_eq,ite_true] using produced
  · have sourceEnough : width (graph.size+1)+2*graph.size≤original.length := by
      by_contra small
      rw [value_short graph start n label empty original (by omega)] at produced
      cases produced
    have window : bits.take (width (graph.size+1)+2*graph.size)=original.take (width (graph.size+1)+2*graph.size) := by
      simp [bits,List.take_append,Nat.sub_eq_zero_of_le sourceEnough]
    rw [← value_take graph start n label bits (by rw [length]; exact enoughSeed),window,
      value_take graph start n label original sourceEnough,produced]

theorem value_isSome_eq (graph : Graph) (start n : ℕ) (label : List Symbol) (first second : List Bool)
    (firstEnough : width (graph.size+1)+2*graph.size≤first.length)
    (secondEnough : width (graph.size+1)+2*graph.size≤second.length) :
    (value graph start n label first).isSome=(value graph start n label second).isSome := by
  by_cases productive : BaseSearch.Productive n <;> by_cases empty : label=[] <;>
    by_cases capacity : encodingLength (graph.size+1)≤n <;>
    cases decoded : decodeLabel (graph.size+1) label <;>
    simp [value,productive,empty,capacity,decoded,firstEnough,secondEnough,Position.value]
  all_goals split_ifs <;> rfl

theorem value_full (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (bits : List Bool) (length : bits.length=seed n) :
    (value graph start n label bits).isSome=true ↔
      (selfReduction.inverseFibre n (graph.encode start) label).Nonempty := by
  constructor
  · intro present
    cases produced : value graph start n label bits with
    | none => simp [produced] at present
    | some word => exact ⟨word,value_sound graph start n member label bits word produced⟩
  · rintro ⟨word,supported⟩
    obtain ⟨first,firstLength,produced⟩ := value_complete_seed graph start n member label word supported
    have enough := seed_enough graph start n label word supported
    have same := value_isSome_eq graph start n label first bits
      (by rw [firstLength]; exact enough) (by rw [length]; exact enough)
    rw [produced] at same
    exact same.symm

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse
