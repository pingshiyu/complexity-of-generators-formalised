import ComplexityOfGenerators.Simulation.CollisionHashOutput

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

theorem collision_hash_terminal (word : BitString) (second : Bool) (frame)
    (source : Configuration M) (input : BitString) (n : ℕ) (output : BitString)
    (bound : frame.inputHead ≤ word.length)
    (inputTape : frame.tape (hashInputTape second) = collisionWord M input)
    (indexTape : frame.tape 2 = collisionWord M (List.replicate n true))
    (observed : M.observe {input := input, index := n} [] source = .halted (.accepted output)) :
    source.output = output ∧ (collisionBank M).Steps word (hashBankConfiguration M second frame source) 3
      {hashBankConfiguration M second frame source with
        state := if second then .resetOutput false else .resetIndex} := by
  cases action : M.transition source.state input[source.inputHead]? none
      (if source.indexHead < n then some () else none) (source.work source.workHead) with
  | accept =>
      exact ⟨by simpa [Machine.observe, action] using observed,
        collision_hash_accept M word second frame source input n bound inputTape indexTape action⟩
  | reject => simp [Machine.observe, action] at observed
  | step next write wm im am ix emit => simp [Machine.observe, action] at observed
  | readRandom no yes => simp [Machine.observe, action] at observed

/-- A terminating deterministic source hash is simulated with linear bank
overhead. The subsequent native compilation accounts for tape-scan overhead. -/
theorem collision_hash_runFrom (deterministic : M.Deterministic)
    (word : BitString) (second : Bool) (frame) (input : BitString) (n : ℕ)
    (bound : frame.inputHead ≤ word.length)
    (inputTape : frame.tape (hashInputTape second) = collisionWord M input)
    (indexTape : frame.tape 2 = collisionWord M (List.replicate n true))
    (t : ℕ) (source : Configuration M) (output : BitString)
    (resources : ReadHeadBounds M {input := input, index := n} source)
    (run : M.runFrom {input := input, index := n} [] source t = .halted (.accepted output)) :
    ∃ ticks last, ticks ≤ 6 * t + 3 ∧ last.output = output ∧ last.indexHead ≤ n ∧
      (collisionBank M).Steps word (hashBankConfiguration M second frame source) ticks
        {hashBankConfiguration M second frame last with
          state := if second then .resetOutput false else .resetIndex} := by
  induction t generalizing source with
  | zero =>
      obtain ⟨emitted, path⟩ := collision_hash_terminal M word second frame source input n output
        bound inputTape indexTape run
      exact ⟨3, source, by omega, emitted, resources.index, path⟩
  | succ t ih =>
      cases observation : M.observe {input := input, index := n} [] source with
      | halted outcome =>
          have same := M.runFrom_halted {input := input, index := n} [] source outcome observation (t + 1)
          rw [run] at same
          cases RunState.halted.inj same
          obtain ⟨emitted, path⟩ := collision_hash_terminal M word second frame source input n output
            bound inputTape indexTape observation
          exact ⟨3, source, by omega, emitted, resources.index, path⟩
      | running current =>
          have same := M.observe_running_eq _ [] source current observation
          subst current
          cases action : M.transition source.state input[source.inputHead]? none
              (if source.indexHead < n then some () else none) (source.work source.workHead) with
          | accept => simp [Machine.observe, action] at observation
          | reject => simp [Machine.observe, action] at observation
          | readRandom no yes =>
              have impossible := deterministic source.state input[source.inputHead]? none
                (if source.indexHead < n then some () else none) (source.work source.workHead)
              simp [action] at impossible
          | step next write wm im am ix emit =>
              let nextSource := M.stepConfiguration {input := input, index := n} source next write wm im am ix emit
              have nextRun : M.next {input := input, index := n} [] source = .running nextSource :=
                M.next_step _ _ _ _ _ _ _ _ _ _ (by simpa using action)
              have remaining : M.runFrom {input := input, index := n} [] nextSource t = .halted (.accepted output) := by
                rw [← M.runFrom_shift _ [] source nextSource observation nextRun t]
                exact run
              obtain ⟨s, cost, step⟩ := collision_hash_next M word second frame source input n bound
                inputTape indexTape resources.input resources.index next write wm im am ix emit action
              obtain ⟨u, last, cost', emitted, index, rest⟩ := ih nextSource
                (resources.stepConfiguration _ _ _ _ _ _ _ _ _ _) remaining
              exact ⟨s + u, last, by omega, emitted, index, step.trans (collisionBank M) rest⟩

end
end ComplexityOfGenerators.Simulation
