import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Commit

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- Check and advance one physical clock mark before making a random choice. -/
theorem random_ready_path (data : InputData I A) (bits : BitString) (fuel used r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded data r source)
    (no yes : Q) (action : B.instruction data source = .readRandom no yes)
    (live : used < fuel) :
    (bank B).Steps data bits (configuration B fuel used source) 2
      {configuration B fuel (used + 1) source with state := .random no yes} := by
  have first : (bank B).Steps data bits (configuration B fuel used source) 1
      {configuration B fuel used source with state := .tickRandom no yes} := by
    apply TapeBank.Steps.go (bank B) data bits _ (.tickRandom no yes)
      bounds.input bounds.auxiliary bounds.index
    rw [fetch_instruction B data fuel used source, action]
    simp [configuration, bank]
  have second : (bank B).Steps data bits
      {configuration B fuel used source with state := .tickRandom no yes} 1
      {configuration B fuel (used + 1) source with state := .random no yes} := by
    have instruction : (bank B).instruction data
        {configuration B fuel used source with state := .tickRandom no yes} =
        .step (.random no yes) (clockTape B fuel used) .right .stay .stay .stay none := by
      simp [TapeBank.instruction, bank, configuration, clockTape, marked, live]
    have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
    simpa only [clock_advance B data fuel used source (.tickRandom no yes) (.random no yes)
      rfl bounds.input bounds.auxiliary bounds.index] using actual
  exact first.trans (bank B) second

theorem random_instruction (data : InputData I A) (fuel used : ℕ)
    (source : BankConfiguration O Q S k) (no yes : Q) :
    (bank B).instruction data
      {configuration B fuel used source with state := .random no yes} =
      .readRandom (.fetch no) (.fetch yes) := rfl

@[simp] theorem random_choose (fuel used : ℕ) (source : BankConfiguration O Q S k)
    (no yes : Q) (bit : Bool) :
    TapeBank.choose {configuration B fuel used source with state := .random no yes}
      (if bit then .fetch yes else .fetch no) =
      configuration B fuel used (TapeBank.choose source (if bit then yes else no)) := by
  cases bit <;> rfl

/-- A source random transition consumes one bit and one clock mark, using exactly
three transitions in the finite bank. -/
theorem random_path (data : InputData I A) (bits : BitString) (fuel used r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded data r source)
    (no yes : Q) (action : B.instruction data source = .readRandom no yes)
    (live : used < fuel) (bit : Bool) (lookup : bits[source.randomHead]? = some bit) :
    (bank B).Steps data bits (configuration B fuel used source) 3
      (configuration B fuel (used + 1) (TapeBank.choose source (if bit then yes else no))) := by
  have first := random_ready_path B data bits fuel used r source bounds no yes action live
  have last : (bank B).Steps data bits
      {configuration B fuel (used + 1) source with state := .random no yes} 1
      (configuration B fuel (used + 1) (TapeBank.choose source (if bit then yes else no))) := by
    apply TapeBank.Steps.random (B := bank B) _ (.fetch no) (.fetch yes) bit 0 _
      (random_instruction B data fuel (used + 1) source no yes) lookup
    rw [random_choose]
    exact .refl _
  exact first.trans (bank B) last

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
