import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Native

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

/-- The callback inspects actual compiled cells. It is unaffected by the
native event step's clearing of its selected head marker. -/
theorem parameter_memory :
    letI := alphabetFintype M
    letI := controlFintype M p
    ∀ (store : Store M) (heads : Fin 80→Option ℤ)
      (memory : ℤ→Option (Fin (machine M p).symbols)) (j : ℕ),
      0<j → store 71=List.replicate (j-1) (factorSymbol M) →
      BankMemory (program M p).bank (fun i=>tape (store i)) heads memory →
      ∀ position : ℕ, parameter M p () (memory position)=decide (position<j) := by
  letI := alphabetFintype M
  letI := controlFintype M p
  intro store heads memory j positive exported represented position
  exact unaryExport_memory (program M p).bank 71 store heads memory j (factorSymbol M)
    positive exported represented position

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
