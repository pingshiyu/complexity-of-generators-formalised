import ComplexityOfGenerators.Simulation.PairCollisionDecisionNative

namespace ComplexityOfGenerators

theorem HashFunction.collisionLanguage_mem_p (h : HashFunction) : h.collisionLanguage∈P PairSymbol := by
  have preimage := Simulation.PairCollisionDecision.polynomial_preimage h.binaryCollisionLanguage_mem_p
  convert preimage using 1
  ext word
  constructor
  · intro member
    exact ⟨word,member,rfl⟩
  · rintro ⟨original,member,equal⟩
    have same := binaryPairWord_injective equal
    simpa [same] using member

end ComplexityOfGenerators
