import ComplexityOfGenerators.Simulation.CollisionBankMemory

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

theorem collision_go (word : BitString)
    (c : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7)
    (next : CollisionPhase M.states M.symbols) (bound : c.inputHead ≤ word.length)
    (table : (collisionBank M).instruction word c = .step next
      (c.tape ((collisionBank M).select c.state) (c.head ((collisionBank M).select c.state))) .stay .stay) :
    (collisionBank M).Steps word c 1 {c with state := next} := by
  have step := TapeBank.Steps.single (collisionBank M) word c next _ .stay .stay table
  rwa [TapeBank.advance_stay _ _ _ _ bound] at step

@[simp] theorem hashBankConfiguration_inputHead (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).head (hashInputTape second) = source.inputHead := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_indexHead (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).head 2 = source.indexHead := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_workHead (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).head (hashWorkTape second) = source.workHead := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_outputHead (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).head (hashOutputTape second) = source.output.length := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_inputTape (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).tape (hashInputTape second) = frame.tape (hashInputTape second) := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_indexTape (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).tape 2 = frame.tape 2 := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_workTape (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).tape (hashWorkTape second) =
      fun i => ⟨none, source.work i⟩ := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

@[simp] theorem hashBankConfiguration_outputTape (second : Bool) (frame) (source : Configuration M) :
    (hashBankConfiguration M second frame source).tape (hashOutputTape second) =
      collisionWord M source.output := by
  cases second <;> simp [hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape]

/-- Fetching the work symbol and input symbol takes two bank instructions;
the unary-index symbol is then available to the actual source transition. -/
theorem collision_hash_fetch (word : BitString) (second : Bool) (frame)
    (source : Configuration M) (input : BitString)
    (bound : frame.inputHead ≤ word.length)
    (inputTape : frame.tape (hashInputTape second) = collisionWord M input) :
    (collisionBank M).Steps word (hashBankConfiguration M second frame source) 2
      {hashBankConfiguration M second frame source with
        state := .hashIndex second source.state (source.work source.workHead)
          input[source.inputHead]? (decide ((source.inputHead : ℤ) = 0))} := by
  let c := hashBankConfiguration M second frame source
  let c₁ := {c with state := CollisionPhase.hashInput second source.state (source.work source.workHead)}
  have first : (collisionBank M).Steps word c 1 c₁ := by
    apply collision_go M word c _ bound
    dsimp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition, c,
      hashBankConfiguration]
    cases second <;> simp [hashInputTape, hashWorkTape, hashOutputTape]
  have last : (collisionBank M).Steps word c₁ 1
      {c with
        state := .hashIndex second source.state (source.work source.workHead)
          input[source.inputHead]? (decide ((source.inputHead : ℤ) = 0))} := by
    apply collision_go M word c₁ _ bound
    simp only [TapeBank.instruction, collisionBank, c₁, collisionSelect, collisionTransition]
    change BankInstruction.step (CollisionPhase.hashIndex second source.state (source.work source.workHead)
        (c.tape (hashInputTape second) (c.head (hashInputTape second))).bit
        (decide (c.head (hashInputTape second) = 0))) _ .stay .stay = _
    simp [c, inputTape]
  exact first.trans (collisionBank M) last

end
end ComplexityOfGenerators.Simulation
