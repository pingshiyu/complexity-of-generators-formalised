import ComplexityOfGenerators.Foundations.ExecutionBounds

/-! A native execution lasting t transitions cannot distinguish a unary
generator index above t+1. This is an operational finite-control fact. -/

namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O)

theorem next_indexHead_le {data : InputData I A} {bits : BitString} {current following : Configuration M}
    (step : M.next data bits current=.running following) : following.indexHead≤current.indexHead+1 := by
  cases action : M.transition current.state data.input[current.inputHead]? data.auxiliary[current.auxiliaryHead]?
      (if current.indexHead<data.index then some () else none) (current.work current.workHead) with
  | accept => simp [Machine.next,action] at step
  | reject => simp [Machine.next,action] at step
  | readRandom no yes =>
      cases lookup : bits[current.randomHead]? with
      | none => simp [Machine.next,action,lookup] at step
      | some bit =>
          simp only [Machine.next,action,lookup,RunState.running.injEq] at step
          subst following
          simp
  | step state write work input auxiliary index emit =>
      rw [M.next_step data bits current state write work input auxiliary index emit action] at step
      have equal := RunState.running.inj step
      subst following
      cases index <;> simp [stepConfiguration,Move.onInput] <;> omega

theorem run_indexHead_le (data : InputData I A) (bits : BitString) (time : ℕ)
    (current : Configuration M) (run : M.run data bits time=.running current) : current.indexHead≤time := by
  induction time generalizing current with
  | zero =>
      have equal := M.observe_running_eq data bits M.initialConfiguration current run
      rw [equal]
      rfl
  | succ time ih =>
      simp only [Machine.run] at run
      cases previous : M.run data bits time with
      | halted result => simp [previous] at run
      | running before =>
          simp only [previous] at run
          cases step : M.next data bits before with
          | halted result => simp [step] at run
          | running following =>
              simp only [step] at run
              rw [M.observe_running_eq data bits following current run]
              have growth := M.next_indexHead_le step
              have old := ih before previous
              omega

end ComplexityOfGenerators.Machine

namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false
variable {O : Type} (M : Machine Unit Bool O)

theorem observe_generatorData_eq_of_indexHead_lt (bits : BitString) (current : Configuration M)
    (first second : ℕ) (left : current.indexHead<first) (right : current.indexHead<second) :
    M.observe (generatorData first) bits current=M.observe (generatorData second) bits current := by
  simp [Machine.observe,generatorData,left,right]

theorem next_generatorData_eq_of_indexHead_add_one_le (bits : BitString) (current : Configuration M)
    (first second : ℕ) (left : current.indexHead+1≤first) (right : current.indexHead+1≤second) :
    M.next (generatorData first) bits current=M.next (generatorData second) bits current := by
  have leftPresent : current.indexHead<first := by omega
  have rightPresent : current.indexHead<second := by omega
  have motion (move : Move) : move.onInput first current.indexHead=move.onInput second current.indexHead := by
    cases move <;> simp [Move.onInput,Nat.min_eq_left left,Nat.min_eq_left right,
      Nat.min_eq_left (by omega : current.indexHead≤first),Nat.min_eq_left (by omega : current.indexHead≤second)]
  simp only [Machine.next,generatorData,List.getElem?_nil,ite_eq_left leftPresent,ite_eq_left rightPresent]
  cases action : M.transition current.state none none (some ()) (current.work current.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes => rfl
  | step state write work input auxiliary index emit =>
      simp only [motion]

theorem run_generatorData_eq_of_large_indices (bits : BitString) (first second time : ℕ)
    (left : time<first) (right : time<second) :
    M.run (generatorData first) bits time=M.run (generatorData second) bits time := by
  induction time with
  | zero =>
      exact M.observe_generatorData_eq_of_indexHead_lt bits M.initialConfiguration first second left right
  | succ time ih =>
      have previousEq := ih (by omega) (by omega)
      simp only [Machine.run,← previousEq]
      cases previous : M.run (generatorData first) bits time with
      | halted result => rfl
      | running current =>
          dsimp only
          have old := M.run_indexHead_le (generatorData first) bits time current previous
          have stepEq := M.next_generatorData_eq_of_indexHead_add_one_le bits current first second (by omega) (by omega)
          rw [← stepEq]
          cases step : M.next (generatorData first) bits current with
          | halted result => rfl
          | running following =>
              have growth := M.next_indexHead_le step
              exact M.observe_generatorData_eq_of_indexHead_lt bits following first second (by omega) (by omega)

theorem run_generatorData_min_index (index time : ℕ) (bits : BitString) :
    M.run (generatorData (min index (time+1))) bits time=M.run (generatorData index) bits time := by
  by_cases small : index≤time+1
  · rw [Nat.min_eq_left small]
  · rw [Nat.min_eq_right (by omega)]
    exact (M.run_generatorData_eq_of_large_indices bits index (time+1) time (by omega) (by omega)).symm

theorem accepted_generatorData_min_index (index time : ℕ) (bits : BitString) (word : List O)
    (accepted : M.run (generatorData index) bits time=.halted (.accepted word)) :
    M.run (generatorData (min index (time+1))) bits time=.halted (.accepted word) := by
  rw [M.run_generatorData_min_index index time bits]
  exact accepted

theorem exists_bounded_index_of_accepted (index time : ℕ) (bits : BitString) (word : List O)
    (accepted : M.run (generatorData index) bits time=.halted (.accepted word)) :
    ∃ boundedIndex,boundedIndex≤time+1 ∧ M.run (generatorData boundedIndex) bits time=.halted (.accepted word) :=
  ⟨min index (time+1),Nat.min_le_right _ _,M.accepted_generatorData_min_index index time bits word accepted⟩

end ComplexityOfGenerators.Machine
