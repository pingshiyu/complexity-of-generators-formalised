import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Value
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Correctness

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse

theorem value_short (graph : Graph) (start n : ℕ) (label : List Symbol) (nonempty : label≠[])
    (bits : List Bool) (short : bits.length<width (graph.size+1)+2*graph.size) :
    value graph start n label bits=none := by
  by_cases productive : BaseSearch.Productive n <;>
    by_cases capacity : encodingLength (graph.size+1)≤n <;>
    cases decoded : decodeLabel (graph.size+1) label <;>
    simp [value,productive,capacity,nonempty,decoded,show ¬width (graph.size+1)+2*graph.size≤bits.length by omega]

theorem value_disabled (graph : Graph) (start n : ℕ) (label : List Symbol) (bits : List Bool)
    (disabled : Classify.enabled n graph.size label=false) : value graph start n label bits=none := by
  by_cases productive : BaseSearch.Productive n <;> by_cases empty : label=[] <;>
    by_cases singletonSize : graph.size=1 <;> by_cases capacity : encodingLength (graph.size+1)≤n <;>
    cases decoded : decodeLabel (graph.size+1) label <;>
    simp_all [Classify.enabled,value,List.isEmpty_iff]

theorem value_decoded (graph : Graph) (start n next position : ℕ) (label : List Symbol) (bits : List Bool)
    (productive : BaseSearch.Productive n) (nonempty : label≠[])
    (capacity : encodingLength (graph.size+1)≤n) (decoded : decodeLabel (graph.size+1) label=some next)
    (enough : width (graph.size+1)+2*graph.size≤bits.length)
    (selected : Position.value graph.size start next (FixedBitBlocks.decode (bits.take (width (graph.size+1))))=some position) :
    value graph start n label bits=some ((graph.insert position
      (rowFromBits ((bits.drop (width (graph.size+1))).take graph.size))
      (forcedRow ((bits.drop (width (graph.size+1)+graph.size)).take graph.size) start)).encode position) := by
  simp [value,productive,nonempty,capacity,decoded,enough,selected]

theorem value_bad_position (graph : Graph) (start n next : ℕ) (label : List Symbol) (bits : List Bool)
    (productive : BaseSearch.Productive n) (nonempty : label≠[])
    (capacity : encodingLength (graph.size+1)≤n) (decoded : decodeLabel (graph.size+1) label=some next)
    (enough : width (graph.size+1)+2*graph.size≤bits.length)
    (selected : Position.value graph.size start next (FixedBitBlocks.decode (bits.take (width (graph.size+1))))=none) :
    value graph start n label bits=none := by
  simp [value,productive,nonempty,capacity,decoded,enough,selected]

theorem block_prefix_parts (bits : List Bool) (blockWidth size : ℕ) :
    (bits.take (blockWidth+2*size)).take blockWidth=bits.take blockWidth ∧
      ((bits.take (blockWidth+2*size)).drop blockWidth).take size=(bits.drop blockWidth).take size ∧
      ((bits.take (blockWidth+2*size)).drop (blockWidth+size)).take size=(bits.drop (blockWidth+size)).take size := by
  have first : blockWidth≤blockWidth+2*size := by omega
  have second : size≤blockWidth+2*size-blockWidth := by omega
  have third : blockWidth+2*size-(blockWidth+size)=size := by omega
  simp [List.take_take,List.drop_take,Nat.min_eq_left first,Nat.min_eq_left second,third]
  omega

theorem value_take (graph : Graph) (start n : ℕ) (label : List Symbol) (bits : List Bool)
    (enough : width (graph.size+1)+2*graph.size≤bits.length) :
    value graph start n label (bits.take (width (graph.size+1)+2*graph.size))=
      value graph start n label bits := by
  obtain ⟨first,second,third⟩ := block_prefix_parts bits (width (graph.size+1)) graph.size
  simp only [value,first,second,third,List.length_take,Nat.min_eq_left enough,
    le_refl,ite_true,ite_eq_left enough]

theorem nextValue_of_decodeLabel (size : ℕ) (label : List Symbol) (next : ℕ)
    (decoded : decodeLabel size label=some next) : nextValue size label=next := by
  have bound := (decodeLabel_sound size label next decoded).1
  have different : next≠size := by omega
  have equation := candidate_eq_decodeLabel size size label
  simp only [decoded,ite_eq_right different] at equation
  unfold candidate at equation
  split_ifs at equation
  exact Option.some.inj equation

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse
