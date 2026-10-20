import ComplexityOfGenerators.Simulation.LibraryTM.Alphabet.Native
import ComplexityOfGenerators.Foundations.Classical

/-! The deterministic direction of the space bridge is unconditional. Library
big-O bounds are first made uniform at every input length, including zero. -/

namespace ComplexityOfGenerators

theorem standard_pspace_subset_pspace : Standard.PSPACE ⊆ PSPACE Bool := by
  intro L member
  obtain ⟨degree, member⟩ := Set.mem_iUnion.mp member
  obtain ⟨n, M, S, decides, asymptotic⟩ := member
  obtain ⟨p, bound⟩ := Complexity.BigO.pow_polynomial_bound asymptotic
  exact Simulation.LibraryTM.mem_pspace M L S decides (PolynomialBound.ofPolynomial p)
    (fun m => (bound m).trans (PolynomialBound.eval_le_ofPolynomial p m))

/-- Transport a binary library language to any finite alphabet through its
bounded unary letter encoding, including the empty alphabet. -/
theorem standard_pspace_encoded_preimage {α : Type} [Fintype α] {L : Language Bool}
    (member : L ∈ Standard.PSPACE) :
    {word : List α | Simulation.NativeNTM.encode word ∈ L} ∈ PSPACE α := by
  obtain ⟨degree, member⟩ := Set.mem_iUnion.mp member
  obtain ⟨n, M, S, decides, asymptotic⟩ := member
  obtain ⟨p, bound⟩ := Complexity.BigO.pow_polynomial_bound asymptotic
  exact Simulation.LibraryTM.Alphabet.mem_pspace_preimage M L S decides
    (PolynomialBound.ofPolynomial p)
    (fun m => (bound m).trans (PolynomialBound.eval_le_ofPolynomial p m))

end ComplexityOfGenerators
