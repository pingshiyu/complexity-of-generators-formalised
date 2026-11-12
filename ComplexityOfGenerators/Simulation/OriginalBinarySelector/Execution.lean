import ComplexityOfGenerators.Simulation.OriginalBinarySelector.Basic

namespace ComplexityOfGenerators.Simulation.OriginalBinarySelector
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G H : Machine Unit Bool α) (p : PolynomialBound)

theorem code_computes (operation : Operation) (n : ℕ) (bits : BitString) :
    ∃ ticks result,(code G H p operation).Runs n bits Command.emptyMemory ticks result ∧
      result.outcome.acceptedWord=referenceValue G H p operation n bits := by
  cases operation with
  | union =>
      obtain ⟨ticks,_,result,run,value⟩ := UnionGenerator.command_runs
        (certificate p G false) (certificate p H true)
        (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
        (width p .union) n _ (UnionGenerator.budgetConditions _ _ _ _ _ n) bits
      exact ⟨ticks,result,by simpa only [code] using run,value⟩
  | concatenation =>
      obtain ⟨ticks,_,result,run,value⟩ := ConcatenationGenerator.command_runs
        (certificate p G false) (certificate p H true)
        (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
        (width p .concatenation) n _ (ConcatenationGenerator.budgetConditions _ _ _ _ _ n) bits
      exact ⟨ticks,result,by simpa only [code] using run,value⟩

theorem code_bounded (operation : Operation) (n : ℕ) (bits : BitString) (short : bits.length≤width p operation n) :
    ∃ ticks≤stackClock G H p operation n,∃ result,
      (code G H p operation).Runs n bits Command.emptyMemory ticks result := by
  cases operation with
  | union =>
      simpa only [code,stackClock] using UnionGenerator.command_time
        (certificate p G false) (certificate p H true)
        (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
        (width p .union) n bits short
  | concatenation =>
      simpa only [code,stackClock] using ConcatenationGenerator.command_time
        (certificate p G false) (certificate p H true)
        (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
        (width p .concatenation) n bits short

theorem native_view (operation : Operation) (n : ℕ) (bits : BitString) (short : bits.length≤width p operation n) :
    UnionGenerator.sourceValue (machine G H p operation) (clock G H p operation) n bits=
      referenceValue G H p operation n bits := by
  exact Command.bounded_sourceValue (code G H p operation) 0 (width p operation)
    (stackClock G H p operation) (referenceValue G H p operation)
    (code_computes G H p operation) (code_bounded G H p operation) n bits short

theorem certificate_view (M : Machine Unit Bool α) (tag : Bool) (n : ℕ) (bits : BitString)
    (length : bits.length=OriginalCertification.seed p n) :
    UnionGenerator.sourceValue (certificate p M tag) (certificateClock p M) n bits=
      (UnionGenerator.sourceValue M (OriginalCertification.clock p) n bits).map
        (fun _=>List.replicate (n+1) tag) :=
  BoundedHeaderCertification.native_view M tag (OriginalCertification.seed p) (OriginalCertification.clock p) n bits length

end
end ComplexityOfGenerators.Simulation.OriginalBinarySelector
