import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Random

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem step_abort (data : InputData I A) (bits : BitString) (fuel r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded data r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O)
    (action : B.instruction data source = .step next write work input auxiliary index emit) :
    (bank B).Executes data bits (configuration B fuel fuel source) 1 .rejected := by
  let waiting : Phase Q S O k :=
    .tickStep (B.select source.state) next write work input auxiliary index emit
  have first : (bank B).Steps data bits (configuration B fuel fuel source) 1
      {configuration B fuel fuel source with state := waiting} := by
    apply TapeBank.Steps.go (bank B) data bits _ waiting
      bounds.input bounds.auxiliary bounds.index
    rw [fetch_instruction B data fuel fuel source, action]
    simp [configuration, bank, waiting]
  have terminal : (bank B).instruction data
      {configuration B fuel fuel source with state := waiting} = .reject := by
    simp [TapeBank.instruction, waiting, bank, configuration, clockTape, marked]
  exact first.executes (bank B) (.reject _ terminal)

theorem random_abort (data : InputData I A) (bits : BitString) (fuel r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded data r source)
    (no yes : Q) (action : B.instruction data source = .readRandom no yes) :
    (bank B).Executes data bits (configuration B fuel fuel source) 1 .rejected := by
  have first : (bank B).Steps data bits (configuration B fuel fuel source) 1
      {configuration B fuel fuel source with state := .tickRandom no yes} := by
    apply TapeBank.Steps.go (bank B) data bits _ (.tickRandom no yes)
      bounds.input bounds.auxiliary bounds.index
    rw [fetch_instruction B data fuel fuel source, action]
    simp [configuration, bank]
  have terminal : (bank B).instruction data
      {configuration B fuel fuel source with state := .tickRandom no yes} = .reject := by
    simp [TapeBank.instruction, bank, configuration, clockTape, marked]
  exact first.executes (bank B) (.reject _ terminal)

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
