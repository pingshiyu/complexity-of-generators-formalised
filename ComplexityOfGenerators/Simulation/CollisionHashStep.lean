import ComplexityOfGenerators.Simulation.CollisionHashFetch

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable (M : Machine Bool Bool Bool)

/-- Update the simulated read-only heads and work tape after the source
instruction has been selected. Output is handled by the following instruction. -/
theorem collision_hash_work_step (word : BitString) (second : Bool) (frame)
    (source : Configuration M) (input : BitString) (n : ℕ)
    (bound : frame.inputHead ≤ word.length)
    (inputTape : frame.tape (hashInputTape second) = collisionWord M input)
    (indexTape : frame.tape 2 = collisionWord M (List.replicate n true))
    (inputBound : source.inputHead ≤ input.length) (indexBound : source.indexHead ≤ n)
    (next : Fin M.states) (write : Option (Fin M.symbols)) (wm im am ix : Move) (emit : Option Bool)
    (table : M.transition source.state input[source.inputHead]? none
      (if source.indexHead < n then some true else none) (source.work source.workHead) =
      .step next write wm im am ix emit) :
    (collisionBank M).Steps word
      {hashBankConfiguration M second frame source with
        state := .hashIndex second source.state (source.work source.workHead)
          input[source.inputHead]? (decide ((source.inputHead : ℤ) = 0))} 3
      {hashBankConfiguration M second frame
          (M.stepConfiguration {input := input, index := n} source next write wm im am ix none) with
        state := match emit with | none => .hashWork second next | some b => .emit second next b} := by
  let B := collisionBank M
  let c := hashBankConfiguration M second frame source
  let im' := collisionReadMove (decide ((source.inputHead : ℤ) = 0)) input[source.inputHead]? im
  let ix' := collisionReadMove (decide ((source.indexHead : ℤ) = 0))
    (if source.indexHead < n then some true else none) ix
  let c₂ := {c with
    state := CollisionPhase.hashIndex second source.state (source.work source.workHead)
      input[source.inputHead]? (decide ((source.inputHead : ℤ) = 0))}
  let c₃ := {c with
    state := CollisionPhase.moveInput second next write wm im' emit
    head := Function.update c.head 2 (ix'.onInt source.indexHead)}
  have indexRead : (List.replicate n true)[source.indexHead]? =
      if source.indexHead < n then some true else none := List.getElem?_replicate
  have indexMove : ix'.onInt source.indexHead = ((ix.onInput n source.indexHead : ℕ) : ℤ) := by
    simpa [ix', indexRead] using collisionReadMove_correct (List.replicate n true)
      source.indexHead (by simpa using indexBound) ix
  have inputMove : im'.onInt source.inputHead = ((im.onInput input.length source.inputHead : ℕ) : ℤ) :=
    collisionReadMove_correct input source.inputHead inputBound im
  have step₃ : B.Steps word c₂ 1 c₃ := by
    have action : B.instruction word c₂ = .step (.moveInput second next write wm im' emit)
        (c₂.tape (B.select c₂.state) (c₂.head (B.select c₂.state))) ix' .stay := by
      simp [B, TapeBank.instruction, c₂, c, collisionBank, collisionSelect, collisionTransition,
        indexTape, indexRead, table, im', ix']
    have run := TapeBank.Steps.single B word c₂ _ _ ix' .stay action
    rw [TapeBank.advance_read B word c₂ _ ix' bound] at run
    simpa [c₂, c₃, B, collisionBank, collisionSelect, c] using run
  let c₄ := {c₃ with
    state := CollisionPhase.writeWork second next write wm emit
    head := Function.update c₃.head (hashInputTape second) (im'.onInt source.inputHead)}
  have step₄ : B.Steps word c₃ 1 c₄ := by
    have action : B.instruction word c₃ = .step (.writeWork second next write wm emit)
        (c₃.tape (B.select c₃.state) (c₃.head (B.select c₃.state))) im' .stay := by
      simp [B, TapeBank.instruction, c₃, collisionBank, collisionSelect, collisionTransition]
    have run := TapeBank.Steps.single B word c₃ _ _ im' .stay action
    rw [TapeBank.advance_read B word c₃ _ im' bound] at run
    convert run using 1
    dsimp [c₄, c₃, B, collisionBank, collisionSelect]
    congr 2
    cases second <;> simp [c, hashInputTape, hashBankConfiguration,
      hashWorkTape, hashOutputTape]
  let resultState : CollisionPhase M.states M.symbols :=
    match emit with | none => .hashWork second next | some b => .emit second next b
  let c₅ := B.advance word c₄ resultState
    {c₄.tape (hashWorkTape second) (c₄.head (hashWorkTape second)) with
      work := write.or (c₄.tape (hashWorkTape second) (c₄.head (hashWorkTape second))).work} wm .stay
  have step₅ : B.Steps word c₄ 1 c₅ := by
    apply TapeBank.Steps.single
    simp [B, TapeBank.instruction, c₄, collisionBank, collisionSelect, collisionTransition,
      resultState, hashWorkTape]
    cases emit <;> rfl
  have equal : c₅ =
      {hashBankConfiguration M second frame
          (M.stepConfiguration {input := input, index := n} source next write wm im am ix none) with
        state := resultState} := by
    apply BankConfiguration.ext
    · rfl
    · exact Nat.min_eq_left bound
    · funext j
      cases second <;>
        simp [c₅, TapeBank.advance, B, collisionBank, collisionSelect, c₄, c₃, c,
          hashBankConfiguration, hashWorkTape, hashOutputTape, hashInputTape,
          Machine.stepConfiguration, indexMove, inputMove, Function.update_apply]
      all_goals split_ifs <;> simp_all
    · funext j i
      cases second <;>
        simp [c₅, TapeBank.advance, B, collisionBank, collisionSelect, c₄, c₃, c,
          hashBankConfiguration, hashWorkTape, hashOutputTape, hashInputTape,
          Machine.stepConfiguration, Function.update_apply]
      all_goals split_ifs <;> simp_all [Option.or]
      all_goals cases write <;> by_cases same : i = source.workHead <;>
        simp_all [Function.update_apply]
  rw [← equal]
  exact (step₃.trans B step₄).trans B step₅

end
end ComplexityOfGenerators.Simulation
