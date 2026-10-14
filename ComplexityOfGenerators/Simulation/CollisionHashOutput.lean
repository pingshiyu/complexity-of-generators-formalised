import ComplexityOfGenerators.Simulation.CollisionHashStep

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable (M : Machine Bool Bool Bool)

theorem collision_hash_emit (word : BitString) (second : Bool) (frame)
    (source : Configuration M) (bit : Bool) (bound : frame.inputHead ≤ word.length) :
    (collisionBank M).Steps word
      {hashBankConfiguration M second frame source with state := .emit second source.state bit} 1
      (hashBankConfiguration M second frame {source with output := source.output ++ [bit]}) := by
  let B := collisionBank M
  let c : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {hashBankConfiguration M second frame source with state := .emit second source.state bit}
  have table : B.instruction word c = .step (.hashWork second source.state) (collisionBit M bit) .right .stay := by
    simp [B, c, TapeBank.instruction, collisionBank, collisionTransition]
  have run := TapeBank.Steps.single B word c _ _ .right .stay table
  convert run using 1
  symm
  apply BankConfiguration.ext
  · rfl
  · exact Nat.min_eq_left bound
  · funext j
    cases second <;> simp [TapeBank.advance, c, B, collisionBank, collisionSelect,
      hashBankConfiguration, hashWorkTape, hashInputTape, hashOutputTape, Move.onInt,
      Function.update_apply]
    all_goals split_ifs <;> simp_all
  · funext j i
    cases second <;> simp [TapeBank.advance, c, B, collisionBank, collisionSelect,
      hashBankConfiguration, hashWorkTape, hashInputTape, hashOutputTape, Function.update_apply,
      ← collisionWord_append M source.output bit]
    all_goals split_ifs <;> simp_all

/-- One original hash instruction takes five bank instructions when silent,
and six when it emits a bit. Each work-tape write is performed explicitly. -/
theorem collision_hash_next (word : BitString) (second : Bool) (frame)
    (source : Configuration M) (input : BitString) (n : ℕ)
    (bound : frame.inputHead ≤ word.length)
    (inputTape : frame.tape (hashInputTape second) = collisionWord M input)
    (indexTape : frame.tape 2 = collisionWord M (List.replicate n true))
    (inputBound : source.inputHead ≤ input.length) (indexBound : source.indexHead ≤ n)
    (next : Fin M.states) (write : Option (Fin M.symbols)) (wm im am ix : Move) (emit : Option Bool)
    (table : M.transition source.state input[source.inputHead]? none
      (if source.indexHead < n then some () else none) (source.work source.workHead) =
      .step next write wm im am ix emit) :
    ∃ t, t ≤ 6 ∧ (collisionBank M).Steps word (hashBankConfiguration M second frame source) t
      (hashBankConfiguration M second frame
        (M.stepConfiguration {input := input, index := n} source next write wm im am ix emit)) := by
  have fetched := collision_hash_fetch M word second frame source input bound inputTape
  have updated := collision_hash_work_step M word second frame source input n bound inputTape indexTape
    inputBound indexBound next write wm im am ix emit table
  have path := fetched.trans (collisionBank M) updated
  cases emit with
  | none => exact ⟨5, by omega, path⟩
  | some bit =>
      have emitted := collision_hash_emit M word second frame
        (M.stepConfiguration {input := input, index := n} source next write wm im am ix none) bit bound
      exact ⟨6, by omega, path.trans (collisionBank M) emitted⟩

/-- An accepting hash observation transfers control to the next stage after
two fetches and one control-transfer instruction. -/
theorem collision_hash_accept (word : BitString) (second : Bool) (frame)
    (source : Configuration M) (input : BitString) (n : ℕ)
    (bound : frame.inputHead ≤ word.length)
    (inputTape : frame.tape (hashInputTape second) = collisionWord M input)
    (indexTape : frame.tape 2 = collisionWord M (List.replicate n true))
    (table : M.transition source.state input[source.inputHead]? none
      (if source.indexHead < n then some () else none) (source.work source.workHead) = .accept) :
    (collisionBank M).Steps word (hashBankConfiguration M second frame source) 3
      {hashBankConfiguration M second frame source with
        state := if second then .resetOutput false else .resetIndex} := by
  have fetched := collision_hash_fetch M word second frame source input bound inputTape
  refine fetched.trans (collisionBank M) (t := 1) ?_
  apply collision_go M word
    {hashBankConfiguration M second frame source with
      state := .hashIndex second source.state (source.work source.workHead)
        input[source.inputHead]? (decide ((source.inputHead : ℤ) = 0))} _ bound
  simp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition,
    indexTape, List.getElem?_replicate, table]

end
end ComplexityOfGenerators.Simulation
