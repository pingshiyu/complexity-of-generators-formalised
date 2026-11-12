import ComplexityOfGenerators.Simulation.PairCollisionDecisionBounds

namespace ComplexityOfGenerators.Simulation.PairCollisionDecision
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (M : Machine Bool Bool Unit)

def program (p : PolynomialBound) := ((routine M p).command.program 0).booleanReturn (checks M)

def machine (p : PolynomialBound) : Machine PairSymbol Bool Unit :=
  InputBank.machine (program M p) 20 21 Cell.pair (fun b=>Cell.source (.auxiliary b))

def verdict (p : PolynomialBound) (word : List PairSymbol) : Outcome Unit :=
  if Program.checksPass (checks M) ((routine M p).eval (loaded M word).store) then .accepted [] else .rejected

theorem program_execution (p : PolynomialBound) (word : List PairSymbol) (bits : BitString) :
    ∃ ticks≤primitiveBudget M p word.length,(program M p).Executes 0 bits
      ((loaded M word).at (program M p).initial) ticks (verdict M p word) := by
  obtain ⟨ticks,cost,run⟩ := (routine M p).runs (n:=0) bits (loaded M word) (by rfl)
  let final : Memory (Cell M) Unit 32 := {loaded M word with store := (routine M p).eval (loaded M word).store}
  have source : ((routine M p).command.program 0).Returns 0 bits (loaded M word) ticks final :=
    run.compiled 0 (by rfl)
  obtain ⟨total,totalCost,execution⟩ := Program.returns_booleanReturn
    ((routine M p).command.program 0) (checks M) (by rfl) source
  have output : final.output=[] := rfl
  rw [output] at execution
  exact ⟨total,totalCost.trans (by have bound:=routine_cost M p word;omega),execution⟩

theorem program_noRandom (p : PolynomialBound) : InputBank.NoRandom (program M p) :=
  Program.booleanReturn_noRandom _ _ ((routine_pure M p).noRandom 0)

theorem machine_deterministic (p : PolynomialBound) : (machine M p).Deterministic :=
  InputBank.machine_deterministic (program M p) 20 21 Cell.pair (fun b=>Cell.source (.auxiliary b))
    (program_noRandom M p)

def time (p : PolynomialBound) : PolynomialBound := InputBank.compiledTime (primitiveTime M p)

theorem machine_runs (p : PolynomialBound) (word : List PairSymbol) (bits : BitString) :
    ∃ ticks≤time M p word.length,(machine M p).run (decisionData word) bits ticks=.halted (verdict M p word) := by
  obtain ⟨ticks,cost,execution⟩ := program_execution M p word bits
  have loadedEq : InputBank.loadedMemory (20 : Fin 32) 21 (Cell.pair : PairSymbol→Cell M)
      (fun b=>Cell.source (.auxiliary b)) (decisionData word)=loaded M word := by
    simp [InputBank.loadedMemory,InputBank.auxiliaryStore,InputBank.inputStore,loaded,decisionData]
  rw [←loadedEq] at execution
  obtain ⟨nativeTicks,nativeCost,native⟩ := InputBank.run_compiled (program M p) 20 21
    Cell.pair (fun b=>Cell.source (.auxiliary b)) (by decide) (decisionData word) bits ticks _ execution
  refine ⟨nativeTicks,nativeCost.trans ?_,native⟩
  apply InputBank.compiledTime_bound (primitiveTime M p) word.length ticks
  exact cost.trans (primitiveBudget_le M p _)

theorem machine_time (p : PolynomialBound) (word : List PairSymbol) :
    (machine M p).TimeBound (decisionData word) (time M p word.length) := by
  intro bits
  obtain ⟨ticks,bound,run⟩ := machine_runs M p word bits
  have padded := (machine M p).run_halted_add (decisionData word) bits ticks (verdict M p word) run
    (time M p word.length-ticks)
  exact ⟨_,by simpa only [Nat.add_sub_of_le bound] using padded⟩

theorem machine_correct (p : PolynomialBound)
    (bounded : ∀ word,M.TimeBound (decisionData word) (p word.length)) (word : List PairSymbol) :
    (machine M p).Accepts (decisionData word) [] ↔ M.Accepts (decisionData (binaryPairWord word)) [] := by
  rw [←checks_correct M p bounded word]
  obtain ⟨ticks,_,run⟩ := machine_runs M p word []
  constructor
  · rintro ⟨output,otherTicks,accepted⟩
    have same := (machine M p).halted_outcome_unique (decisionData word) [] ticks otherTicks
      (verdict M p word) (.accepted output) run accepted
    cases decision : Program.checksPass (checks M) ((routine M p).eval (loaded M word).store) <;>
      simp [verdict,decision] at same ⊢
  · intro decision
    exact ⟨[],ticks,by simpa [verdict,decision] using run⟩

theorem polynomial_preimage {L : Language Bool} (member : L∈P Bool) :
    {word : List PairSymbol | binaryPairWord word∈L}∈P PairSymbol := by
  obtain ⟨source,p,deterministic,bounded,correct⟩ := member
  refine ⟨machine source p,time source p,machine_deterministic source p,machine_time source p,?_⟩
  intro word
  rw [machine_correct source p bounded word]
  exact correct (binaryPairWord word)

end
end ComplexityOfGenerators.Simulation.PairCollisionDecision
