import ComplexityOfGenerators.Simulation.WordStack.RandomFree

/-! A finite deterministic terminal predicate for stack programs. Returning
from the source program transfers to three explicit stack-head tests; failing
a test rejects natively. No output inspection or random exhaustion is used. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Program

set_option backward.isDefEq.respectTransparency false

variable {Q S O : Type} {k : ℕ}

abbrev BooleanChecks (S : Type) (k : ℕ) := Fin 3 → Fin k × (Option S → Bool)

def checksPass (checks : BooleanChecks S k) (s : Local.Store S k) : Bool :=
  (checks 0).2 (s (checks 0).1).head? && (checks 1).2 (s (checks 1).1).head? &&
    (checks 2).2 (s (checks 2).1).head?

def booleanReturn (P : Program Q S O k) (checks : BooleanChecks S k) : Program (Q ⊕ Fin 3) S O k where
  initial := .inl P.initial
  select := Sum.elim P.select (fun i => (checks i).1)
  transition := fun state cell index => match state with
    | .inl state => Instruction.redirect Sum.inl (.step (.inr 0) .stay .stay none)
        (P.transition state cell index)
    | .inr i => if (checks i).2 cell then
        if i = 0 then .step (.inr 1) .stay .stay none
        else if i = 1 then .step (.inr 2) .stay .stay none
        else .accept
      else .reject

theorem booleanReturn_embeds (P : Program Q S O k) (checks : BooleanChecks S k) :
    P.Embeds (P.booleanReturn checks) Sum.inl := by
  constructor
  · intro state; rfl
  · intro state cell input next action index emit table
    simp [booleanReturn, table, Instruction.redirect]
  · intro state cell input no yes table
    simp [booleanReturn, table, Instruction.redirect]

theorem booleanReturn_checks (P : Program Q S O k) (checks : BooleanChecks S k)
    (n : ℕ) (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    ∃ ticks ≤ 2, (P.booleanReturn checks).Executes n bits (m.at (.inr 0)) ticks
      (if checksPass checks m.store then .accepted m.output else .rejected) := by
  let T := P.booleanReturn checks
  by_cases first : (checks 0).2 (m.store (checks 0).1).head? = true
  · have firstStep : T.Steps n bits (m.at (.inr 0)) 1 (m.at (.inr 1)) := by
      apply Steps.go_at _ n bits m _ _ bounded
      simp [T, instruction, Memory.at, Configuration.mapState, booleanReturn, first]
    by_cases second : (checks 1).2 (m.store (checks 1).1).head? = true
    · have secondStep : T.Steps n bits (m.at (.inr 1)) 1 (m.at (.inr 2)) := by
        apply Steps.go_at _ n bits m _ _ bounded
        simp [T, instruction, Memory.at, Configuration.mapState, booleanReturn, second]
      by_cases third : (checks 2).2 (m.store (checks 2).1).head? = true
      · have accepted : T.Executes n bits (m.at (.inr 2)) 0 (.accepted m.output) := by
          apply Executes.accept
          simp [T, instruction, Memory.at, Configuration.mapState, booleanReturn, third]
        refine ⟨2, by omega, ?_⟩
        simpa [checksPass, first, second, third] using (firstStep.trans T secondStep).executes T accepted
      · have rejected : T.Executes n bits (m.at (.inr 2)) 0 .rejected := by
          apply Executes.reject
          simp [T, instruction, Memory.at, Configuration.mapState, booleanReturn, third]
        refine ⟨2, by omega, ?_⟩
        simpa [checksPass, first, second, third] using (firstStep.trans T secondStep).executes T rejected
    · have rejected : T.Executes n bits (m.at (.inr 1)) 0 .rejected := by
        apply Executes.reject
        simp [T, instruction, Memory.at, Configuration.mapState, booleanReturn, second]
      refine ⟨1, by omega, ?_⟩
      simpa [checksPass, first, second] using firstStep.executes T rejected
  · have rejected : T.Executes n bits (m.at (.inr 0)) 0 .rejected := by
      apply Executes.reject
      simp [T, instruction, Memory.at, Configuration.mapState, booleanReturn, first]
    refine ⟨0, by omega, ?_⟩
    simpa [checksPass, first] using rejected

theorem returns_booleanReturn (P : Program Q S O k) (checks : BooleanChecks S k)
    {n : ℕ} {bits : BitString} {start finish : Memory S O k} {ticks : ℕ}
    (bounded : start.indexHead ≤ n) (run : P.Returns n bits start ticks finish) :
    ∃ total ≤ ticks + 3,
      (P.booleanReturn checks).Executes n bits (start.at (.inl P.initial)) total
        (if checksPass checks finish.store then .accepted finish.output else .rejected) := by
  obtain ⟨state, path, terminal⟩ := run
  have embedded := (booleanReturn_embeds P checks).steps P path
  have finishBound := path.index_le P bounded
  have transfer : (P.booleanReturn checks).Steps n bits (finish.at (.inl state)) 1 (finish.at (.inr 0)) := by
    apply Steps.go_at _ n bits finish _ _ finishBound
    change Instruction.redirect Sum.inl _ (P.instruction n (finish.at state)) = _
    rw [terminal]
    rfl
  obtain ⟨remaining, cost, tail⟩ := booleanReturn_checks P checks n bits finish finishBound
  refine ⟨ticks + 1 + remaining, by omega, ?_⟩
  exact (embedded.trans _ transfer).executes _ tail

theorem booleanReturn_noRandom (P : Program Q S O k) (checks : BooleanChecks S k)
    (pure : InputBank.NoRandom P) : InputBank.NoRandom (P.booleanReturn checks) := by
  intro state cell index
  cases state with
  | inl state =>
    have source := pure state cell index
    cases command : P.transition state cell index <;> simp_all [booleanReturn, Instruction.redirect]
  | inr state =>
    by_cases pass : (checks state).2 cell <;> fin_cases state <;> simp_all [booleanReturn]

end ComplexityOfGenerators.Simulation.WordStack.Program
