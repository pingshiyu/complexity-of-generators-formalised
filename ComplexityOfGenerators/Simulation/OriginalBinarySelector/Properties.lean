import ComplexityOfGenerators.Simulation.OriginalBinarySelector.Execution
import ComplexityOfGenerators.Proofs.OriginalCertification.HeaderBridge

/-! Exact native selector views on the very same random blocks used by the
original-source first-moment samplers. -/
namespace ComplexityOfGenerators.Simulation.OriginalBinarySelector
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)

theorem native_union_view (n : ℕ) (bits : BitString) (length : bits.length=width p .union n) :
    UnionGenerator.sourceValue (machine (families false).machine (families true).machine p .union)
      (clock (families false).machine (families true).machine p .union) n bits=
      (OriginalCertification.Union.choice families p n bits).map
        (fun tag => OriginalCertification.HeaderBridge.header tag n) := by
  rw [native_view (families false).machine (families true).machine p .union n bits length.le]
  simp only [referenceValue,←length,le_refl,↓reduceIte,List.take_length]
  exact OriginalCertification.HeaderBridge.union_value families
    (certificate p (families false).machine false) (certificate p (families true).machine true) p
    (certificateClock p (families false).machine) (certificateClock p (families true).machine)
    (certificate_view p (families false).machine false) (certificate_view p (families true).machine true)
    n bits (by simpa only [width] using length.ge)

theorem native_concat_view (n : ℕ) (bits : BitString) (length : bits.length=width p .concatenation n) :
    UnionGenerator.sourceValue (machine (families false).machine (families true).machine p .concatenation)
      (clock (families false).machine (families true).machine p .concatenation) n bits=
      (OriginalCertification.Concatenation.choice families p n bits).map
        (OriginalCertification.HeaderBridge.concatHeader n) := by
  rw [native_view (families false).machine (families true).machine p .concatenation n bits length.le]
  simp only [referenceValue,←length,le_refl,↓reduceIte,List.take_length]
  exact OriginalCertification.HeaderBridge.concat_value families
    (certificate p (families false).machine false) (certificate p (families true).machine true) p
    (certificateClock p (families false).machine) (certificateClock p (families true).machine)
    (certificate_view p (families false).machine false) (certificate_view p (families true).machine true)
    n bits (by simpa only [width] using length.ge)

end
end ComplexityOfGenerators.Simulation.OriginalBinarySelector
