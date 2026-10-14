import ComplexityOfGenerators.Simulation.TransducerBank.Time
import ComplexityOfGenerators.Foundations.RandomTapeShift

/-! Native nondeterministic choice between two deciders. The initial random bit
selects the transition table, and the remaining tape is the selected choice tape.
A finite tape bank shares a tagged work alphabet between the two branches. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Bool → Machine α Bool Unit)

abbrev ChoiceState := Option (Σ b : Bool, Fin (M b).states)
abbrev ChoiceSymbol := Option (Σ b : Bool, Fin (M b).symbols)

def choiceRead (b : Bool) : ChoiceSymbol M → Option (Fin (M b).symbols)
  | none => none
  | some ⟨a, s⟩ => if equal : a = b then some (equal ▸ s) else none

@[simp] theorem choiceRead_map (b : Bool) (s : Option (Fin (M b).symbols)) :
    choiceRead M b (s.map (Sigma.mk b)) = s := by cases s <;> simp [choiceRead]

def choiceWrite (b : Bool) (cell : ChoiceSymbol M) : Option (Fin (M b).symbols) → ChoiceSymbol M
  | none => cell
  | some s => some ⟨b, s⟩

def choiceInstruction (b : Bool) (cell : ChoiceSymbol M) :
    Instruction Unit (M b).states (M b).symbols → TransducerBank.BankInstruction (ChoiceState M) (ChoiceSymbol M) Unit
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (some ⟨b, no⟩) (some ⟨b, yes⟩)
  | .step next write work input _ _ _ =>
      .step (some ⟨b, next⟩) (choiceWrite M b cell write)
        work input .stay .stay none

def choiceBank : TransducerBank.TapeBank α Bool Unit (ChoiceState M) (ChoiceSymbol M) 1 where
  initial := none
  blank := none
  select := fun _ => 0
  transition := fun q input _ _ _ cell => match q with
    | none => .readRandom (some ⟨false, (M false).initial⟩) (some ⟨true, (M true).initial⟩)
    | some ⟨b, q⟩ => choiceInstruction M b cell ((M b).transition q input none none (choiceRead M b cell))

def choiceConfiguration (b : Bool) (c : Configuration (M b)) :
    TransducerBank.BankConfiguration Unit (ChoiceState M) (ChoiceSymbol M) 1 where
  state := some ⟨b, c.state⟩
  inputHead := c.inputHead
  auxiliaryHead := 0
  indexHead := 0
  randomHead := c.randomHead + 1
  output := []
  head := fun _ => c.workHead
  tape := fun _ i => (c.work i).map (Sigma.mk b)

def choiceOutcome : Outcome Unit → Outcome Unit
  | .accepted _ => .accepted []
  | .rejected => .rejected
  | .exhausted => .exhausted

theorem choice_advance (b : Bool) (word : List α) (c : Configuration (M b))
    (next : Fin (M b).states) (write : Option (Fin (M b).symbols))
    (work input auxiliary index : Move) (emit : Option Unit) :
    (choiceBank M).advance (decisionData word) (choiceConfiguration M b c) (some ⟨b, next⟩)
        (choiceWrite M b ((c.work c.workHead).map (Sigma.mk b)) write)
        work input .stay .stay none =
      choiceConfiguration M b {c with
        state := next
        inputHead := input.onInput word.length c.inputHead
        auxiliaryHead := auxiliary.onInput 0 c.auxiliaryHead
        indexHead := index.onInput 0 c.indexHead
        workHead := work.onInt c.workHead
        work := match write with | none => c.work | some s => Function.update c.work c.workHead (some s)
        visited := insert (work.onInt c.workHead) c.visited
        output := c.output ++ emit.toList} := by
  apply TransducerBank.BankConfiguration.ext
  all_goals try rfl
  · funext j
    fin_cases j
    simp [TransducerBank.TapeBank.advance, choiceBank, choiceConfiguration]
  · funext j i
    fin_cases j
    simp only [TransducerBank.TapeBank.advance, choiceBank, choiceConfiguration, Function.update_self]
    cases write with
    | none => simp [choiceWrite, Function.update_eq_self]
    | some s => by_cases same : i = c.workHead <;> simp [choiceWrite, same]

theorem choice_terminal (b : Bool) (word : List α) (bits : BitString) (c : Configuration (M b))
    (result : Outcome Unit) (source : (M b).observe (decisionData word) bits c = .halted result) :
    (choiceBank M).Executes (decisionData word) (b :: bits) (choiceConfiguration M b c) 0 (choiceOutcome result) := by
  cases action : (M b).transition c.state word[c.inputHead]? none none (c.work c.workHead) with
  | accept =>
      have equal : result = .accepted c.output := by simpa [Machine.runFrom, Machine.observe, decisionData, action] using source.symm
      subst result
      apply TransducerBank.TapeBank.Executes.accept
      simp [TransducerBank.TapeBank.instruction, choiceBank, choiceConfiguration, choiceInstruction, decisionData, action]
  | reject =>
      have equal : result = .rejected := by simpa [Machine.runFrom, Machine.observe, decisionData, action] using source.symm
      subst result
      apply TransducerBank.TapeBank.Executes.reject
      simp [TransducerBank.TapeBank.instruction, choiceBank, choiceConfiguration, choiceInstruction, decisionData, action]
  | step next write work input auxiliary index emit => simp [Machine.runFrom, Machine.observe, decisionData, action] at source
  | readRandom no yes =>
      have absent : ¬ c.randomHead < bits.length := by
        intro available
        simp [Machine.runFrom, Machine.observe, decisionData, action, available] at source
      have equal : result = .exhausted := by simpa [Machine.runFrom, Machine.observe, decisionData, action, absent] using source.symm
      subst result
      apply TransducerBank.TapeBank.Executes.exhausted _ (some ⟨b, no⟩) (some ⟨b, yes⟩)
      · simp [TransducerBank.TapeBank.instruction, choiceBank, choiceConfiguration, choiceInstruction, decisionData, action]
      · simpa [choiceConfiguration] using List.getElem?_eq_none (Nat.le_of_not_gt absent)

theorem choice_executes (b : Bool) (word : List α) (bits : BitString) (c : Configuration (M b))
    (t : ℕ) (result : Outcome Unit) (source : (M b).runFrom (decisionData word) bits c t = .halted result) :
    ∃ ticks, ticks ≤ t ∧ (choiceBank M).Executes (decisionData word) (b :: bits) (choiceConfiguration M b c) ticks (choiceOutcome result) := by
  induction t generalizing c with
  | zero => exact ⟨0, le_rfl, choice_terminal M b word bits c result source⟩
  | succ t ih =>
      cases observation : (M b).observe (decisionData word) bits c with
      | halted out =>
          have same := (M b).runFrom_halted (decisionData word) bits c out observation (t + 1)
          rw [source] at same
          cases same
          exact ⟨0, by omega, choice_terminal M b word bits c result observation⟩
      | running d =>
          have equal := (M b).observe_running_eq _ bits c d observation
          subst d
          obtain ⟨d, next⟩ := (M b).next_running_of_observe_running _ bits c observation
          rw [(M b).runFrom_shift _ bits c d observation next t] at source
          cases action : (M b).transition c.state word[c.inputHead]? none none (c.work c.workHead) with
          | accept => simp [Machine.observe, decisionData, action] at observation
          | reject => simp [Machine.observe, decisionData, action] at observation
          | step state write work input auxiliary index emit =>
              rw [(M b).next_step _ bits c state write work input auxiliary index emit (by simpa [decisionData] using action)] at next
              cases next
              obtain ⟨ticks, bound, execution⟩ := ih _ source
              refine ⟨ticks + 1, by omega, .step _ (some ⟨b, state⟩)
                (choiceWrite M b ((c.work c.workHead).map (Sigma.mk b)) write)
                work input .stay .stay none ticks _ ?_ ?_⟩
              · simp [TransducerBank.TapeBank.instruction, choiceBank, choiceConfiguration, choiceInstruction, decisionData, action]
              · rw [choice_advance M b word c state write work input auxiliary index emit]
                cases write <;> cases emit <;> exact execution
          | readRandom no yes =>
              cases lookup : bits[c.randomHead]? with
              | none => simp [Machine.next, decisionData, action, lookup] at next
              | some letter =>
                  simp only [Machine.next, decisionData, List.getElem?_nil, Nat.not_lt_zero, ↓reduceIte,
                    action, lookup, RunState.running.injEq] at next
                  subst d
                  obtain ⟨ticks, bound, execution⟩ := ih _ source
                  refine ⟨ticks + 1, by omega, .random _ (some ⟨b, no⟩) (some ⟨b, yes⟩) letter ticks _ ?_ ?_ ?_⟩
                  · simp [TransducerBank.TapeBank.instruction, choiceBank, choiceConfiguration, choiceInstruction, decisionData, action]
                  · simpa [choiceConfiguration] using lookup
                  · cases letter <;> exact execution

end
end ComplexityOfGenerators.Simulation
