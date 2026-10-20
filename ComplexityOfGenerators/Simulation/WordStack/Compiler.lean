import ComplexityOfGenerators.Simulation.WordStack.Basic

/-! Quantitative compilation of word-stack programs. A push takes two bank
steps; every other nonterminal instruction takes one. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Program

open TransducerBank

variable {Q S O : Type} {k : ℕ} (P : Program Q S O k)

theorem encoded_instruction (n : ℕ) (c : Configuration Q S O k) :
    P.bank.instruction (generatorData n) (P.encoded c) =
      match P.instruction n c with
      | .accept => .accept
      | .reject => .reject
      | .random no yes => .readRandom (.ready no) (.ready yes)
      | .step next .stay index emit => .step (.ready next) (c.store (P.select c.state)).head?
          .stay .stay .stay index emit
      | .step next (.push a) index emit => .step (.push next (P.select c.state) a)
          (c.store (P.select c.state)).head? .right .stay .stay index emit
      | .step next .pop index emit => .step (.ready next) none
          (if c.store (P.select c.state) = [] then .stay else .left) .stay .stay index emit := by
  classical
  simp [TapeBank.instruction, bank, bankSelect, encoded, generatorData, tape_head,
    bankTransition, instruction, List.length_eq_zero_iff]
  rfl

theorem encoded_choose (c : Configuration Q S O k) (next : Q) :
    P.encoded (choose c next) = TapeBank.choose (P.encoded c) (.ready next) := rfl

theorem advance_stay (n : ℕ) (c : Configuration Q S O k) (next : Q)
    (index : Move) (emit : Option O) :
    P.bank.advance (generatorData n) (P.encoded c) (.ready next)
      (c.store (P.select c.state)).head? .stay .stay .stay index emit =
        P.encoded (P.advance n c next .stay index emit) := by
  simp only [TapeBank.advance, bank, bankSelect, encoded, advance, Action.apply,
    generatorData, Move.onInput, Move.onInt, Function.update_eq_self]
  congr 1
  rw [← tape_head, Function.update_eq_self, Function.update_eq_self]

theorem advance_pop (n : ℕ) (c : Configuration Q S O k) (next : Q)
    (index : Move) (emit : Option O) :
    P.bank.advance (generatorData n) (P.encoded c) (.ready next) none
      (if c.store (P.select c.state) = [] then .stay else .left) .stay .stay index emit =
        P.encoded (P.advance n c next .pop index emit) := by
  classical
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, bank, bankSelect, encoded, advance, Action.apply,
      generatorData, Move.onInput, List.length_nil, Nat.min_zero]
  · funext j
    by_cases same : j = P.select c.state
    · subst j
      simp only [Function.update_self, List.length_tail]
      cases h : c.store (P.select c.state) with
      | nil => simp [Move.onInt]
      | cons a xs => simp [Move.onInt]
    · simp [same]
  · funext j
    by_cases same : j = P.select c.state
    · subst j
      simp only [Function.update_self]
      exact (tape_pop _).symm
    · simp [same]

def pushing (n : ℕ) (c : Configuration Q S O k) (next : Q) (a : S)
    (index : Move) (emit : Option O) : BankConfiguration O (Phase Q S k) (Option S) k :=
  P.bank.advance (generatorData n) (P.encoded c) (.push next (P.select c.state) a)
    (c.store (P.select c.state)).head? .right .stay .stay index emit

theorem pushing_instruction (n : ℕ) (c : Configuration Q S O k) (next : Q) (a : S)
    (index : Move) (emit : Option O) :
    P.bank.instruction (generatorData n) (P.pushing n c next a index emit) =
      .step (.ready next) (some a) .stay .stay .stay .stay none := rfl

theorem advance_push (n : ℕ) (c : Configuration Q S O k) (bounded : c.indexHead ≤ n)
    (next : Q) (a : S)
    (index : Move) (emit : Option O) :
    P.bank.advance (generatorData n) (P.pushing n c next a index emit)
      (.ready next) (some a) .stay .stay .stay .stay none =
        P.encoded (P.advance n c next (.push a) index emit) := by
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, pushing, bank, bankSelect, encoded, advance, Action.apply,
      generatorData, Move.onInput, Move.onInt, List.length_nil, Nat.min_zero,
      Option.toList_none, List.append_nil, Function.update_self, Function.update_idem]
  · exact Nat.min_eq_left (index.onInput_le n c.indexHead bounded)
  · funext j
    by_cases same : j = P.select c.state
    · subst j
      simp
    · simp [same]
  · funext j
    by_cases same : j = P.select c.state
    · subst j
      simp only [Function.update_self, ← tape_head, Function.update_eq_self]
      exact (tape_push _ _).symm
    · simp [same]

theorem step_compiled {n : ℕ} {bits : BitString} {c : Configuration Q S O k}
    (bounded : c.indexHead ≤ n) {next : Q} {action : Action S} {index : Move} {emit : Option O}
    (table : P.instruction n c = .step next action index emit) :
    ∃ ticks, ticks ≤ 2 ∧ P.bank.Steps (generatorData n) bits (P.encoded c) ticks
      (P.encoded (P.advance n c next action index emit)) := by
  classical
  have table' := P.encoded_instruction n c
  rw [table] at table'
  cases action with
  | stay =>
    refine ⟨1, by omega, ?_⟩
    simpa only [P.advance_stay] using TapeBank.Steps.single P.bank _ bits _ _ _ _ _ _ _ _ table'
  | pop =>
    refine ⟨1, by omega, ?_⟩
    simpa only [P.advance_pop] using TapeBank.Steps.single P.bank _ bits _ _ _ _ _ _ _ _ table'
  | push a =>
    refine ⟨2, by omega, ?_⟩
    apply TapeBank.Steps.step _ _ _ _ _ _ _ _ 1 _ table'
    change P.bank.Steps (generatorData n) bits (P.pushing n c next a index emit) 1 _
    simpa only [P.advance_push n c bounded] using
      TapeBank.Steps.single P.bank _ bits _ _ _ _ _ _ _ _ (P.pushing_instruction n c next a index emit)

theorem executes_compiled {n : ℕ} {bits : BitString} {c : Configuration Q S O k}
    {t : ℕ} {result : Outcome O} (exec : P.Executes n bits c t result)
    (bounded : c.indexHead ≤ n) :
    ∃ ticks, ticks ≤ 2 * t ∧ P.bank.Executes (generatorData n) bits (P.encoded c) ticks result := by
  induction exec with
  | accept c table =>
    exact ⟨0, by omega, .accept _ (by rw [P.encoded_instruction, table])⟩
  | reject c table =>
    exact ⟨0, by omega, .reject _ (by rw [P.encoded_instruction, table])⟩
  | exhausted c no yes table absent =>
    exact ⟨0, by omega, .exhausted _ _ _ (by rw [P.encoded_instruction, table]) absent⟩
  | random c no yes bit t result table lookup rest ih =>
    obtain ⟨ticks, bound, run⟩ := ih bounded
    refine ⟨ticks + 1, by omega, .random _ _ _ bit ticks result
      (by rw [P.encoded_instruction, table]) lookup ?_⟩
    simpa only [P.encoded_choose, apply_ite Phase.ready] using run
  | step c next action index emit t result table rest ih =>
    obtain ⟨s, cost, path⟩ := P.step_compiled bounded table (bits := bits)
    obtain ⟨ticks, bound, run⟩ := ih (index.onInput_le _ _ bounded)
    exact ⟨s + ticks, by omega, path.executes P.bank run⟩

noncomputable def machine [Fintype Q] [Fintype S] [Fintype O] : Machine Unit Bool O :=
  bankMachine P.bank

/-- End-to-end compilation includes initialization and the tape-bank scans. -/
theorem run_compiled [Fintype Q] [Fintype S] [Fintype O]
    {n : ℕ} {bits : BitString} {t : ℕ} {result : Outcome O}
    (exec : P.Executes n bits P.initialConfiguration t result) :
    ∃ ticks, ticks ≤ 1 + (2 * t + 1) * (4 * t + 4) ∧
      P.machine.run (generatorData n) bits ticks = .halted result := by
  obtain ⟨s, bound, run⟩ := P.executes_compiled exec (Nat.zero_le _)
  rw [P.encoded_initial] at run
  obtain ⟨ticks, cost, run⟩ := bank_run P.bank _ bits s result run
  refine ⟨ticks, cost.trans ?_, run⟩
  nlinarith

end ComplexityOfGenerators.Simulation.WordStack.Program
