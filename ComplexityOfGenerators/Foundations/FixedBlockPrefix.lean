import ComplexityOfGenerators.Foundations.FixedBlockRetries
import ComplexityOfGenerators.Foundations.StreamSemantics

namespace ComplexityOfGenerators

/-- A possibly longer stream prefix retains every complete earlier block. -/
theorem streamPrefix_drop_take_fixedBlock_of_le (width : ℕ) (stream : BitStream) (index total : ℕ)
    (fits : (index+1)*width≤total) :
    ((streamPrefix stream total).drop (index*width)).take width=List.ofFn (fixedBlock width stream index) := by
  have full : index*width+width≤total := by nlinarith
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,streamPrefix_length,List.length_ofFn]
    omega
  · intro j before _
    simp only [List.getElem_take,List.getElem_drop,streamPrefix,List.getElem_ofFn,fixedBlock]

/-- A complete prefix ending after phase N contains exactly the ith fixed
block at its ith block position. -/
theorem streamPrefix_drop_take_fixedBlock (k : ℕ) (stream : BitStream) (i N : ℕ) (index : i ≤ N) :
    ((streamPrefix stream ((N+1)*k)).drop (i*k)).take k = List.ofFn (fixedBlock k stream i) :=
  streamPrefix_drop_take_fixedBlock_of_le k stream i ((N+1)*k)
    (Nat.mul_le_mul_right k (Nat.add_le_add_right index 1))

end ComplexityOfGenerators
