import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Label

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] InverseNative.bodyTransform transform NativeSubstitution.prepareStream parse

def indexed (n : ℕ) (target label : List Symbol) : Memory := Command.loadedIndex 32 .zero n (loaded target label)

def sized (n : ℕ) (target label : List Symbol) : Memory :=
  {prepared n target label with store := sizeTest.eval (preparedStore n target label)}

def parsed (n : ℕ) (target label : List Symbol) : Memory :=
  {sized n target label with store := parse.eval (sized n target label).store}

def commandBudget (n : ℕ) (target label : List Symbol) (bits : BitString) : ℕ :=
  3*n+inputRoutine.cost (indexed n target label).store+sizeTest.cost (preparedStore n target label)+
    parse.cost (sized n target label).store+labelBudget n bits (parsed n target label)+bits.length+10

theorem command_runs_canonical {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (label : List Symbol) (bits : BitString) :
    ∃ ticks ≤ commandBudget n (formula.encode capacity active) label bits, ∃ result,
      command.Runs n bits (loaded (formula.encode capacity active) label) ticks result ∧
        result.outcome = valueOutcome (value n (formula.encode capacity active) label bits) := by
  let target := formula.encode capacity active
  have loadRun := Command.loadIndex_runs (O := Symbol) (32 : Fin 35) Symbol.zero n bits (loaded target label) (Nat.zero_le _)
  obtain ⟨inputTicks,inputCost,inputRun⟩ := inputRoutine.runs (n := n) bits (indexed n target label) le_rfl
  have readyEq : {indexed n target label with store := inputRoutine.eval (indexed n target label).store} =
      prepared n target label := by
    rw [show (indexed n target label).store = (Command.loadedIndex 32 .zero n (loaded target label)).store from rfl,inputRoutine_value]
    rfl
  rw [readyEq] at inputRun
  obtain ⟨sizeTicks,sizeCost,sizeRun⟩ := sizeTest.runs (n := n) bits (prepared n target label) le_rfl
  change sizeTest.command.Runs n bits (prepared n target label) sizeTicks (.done (sized n target label)) at sizeRun
  have flag : ((sized n target label).store 33).head?.isSome = decide (target.length = n) := sizeTest_flag n target label
  by_cases equal : target.length = n
  · obtain ⟨parseTicks,parseCost,parseRun⟩ := parse.runs (n := n) bits (sized n target label) le_rfl
    change parse.command.Runs n bits (sized n target label) parseTicks (.done (parsed n target label)) at parseRun
    have originalWord : (sized n target label).store 2 = target := by
      rw [show (sized n target label).store 2 = sizeTest.eval (preparedStore n target label) 2 from rfl,
        sizeTest_frame _ _ (by decide) (by decide) (by decide) (by decide)]
      simp [preparedStore]
    have originalLabel : (sized n target label).store 3 = label := by
      rw [show (sized n target label).store 3 = sizeTest.eval (preparedStore n target label) 3 from rfl,
        sizeTest_frame _ _ (by decide) (by decide) (by decide) (by decide)]
      simp [preparedStore]
    have originalCounter : (sized n target label).store 32 = List.replicate n .zero := by
      rw [show (sized n target label).store 32 = sizeTest.eval (preparedStore n target label) 32 from rfl,
        sizeTest_frame _ _ (by decide) (by decide) (by decide) (by decide)]
      simp [preparedStore]
    have originalSaved : (sized n target label).store 34 = target := by
      rw [show (sized n target label).store 34 = sizeTest.eval (preparedStore n target label) 34 from rfl,
        sizeTest_frame _ _ (by decide) (by decide) (by decide) (by decide)]
      simp [preparedStore]
    have properties := parse_canonical bound formula (sized n target label).store originalWord
    have counter : (parsed n target label).store 32 = List.replicate n .zero :=
      (parse_upper _ 32 (by decide)).trans originalCounter
    have contents : (parsed n target label).store 3 = label := (parse_label _).trans originalLabel
    have saved : (parsed n target label).store 34 = target := (parse_upper _ 34 (by decide)).trans originalSaved
    have clock : NativeBody.tokenCount formula ≤ ((parsed n target label).store 16).length := by
      rw [show ((parsed n target label).store 16).length = (formula.bodyWord capacity).length from properties.2]
      exact NativeBody.tokenCount_bound bound formula valid
    obtain ⟨lastTicks,lastCost,result,lastRun,outcome⟩ := selectLabel_runs bound formula valid n bits
      (parsed n target label) le_rfl counter properties.1 clock rfl rfl label contents
    have total := Command.Runs.seq _ _ _ _ _ _ _ parseRun lastRun
    have after : afterSize.Runs n bits (sized n target label) (1+(parseTicks+1+lastTicks)) result := by
      apply Command.Runs.branch
      simpa only [observe,flag,decide_eq_true equal,ite_true] using total
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun
      (Command.Runs.seq _ _ _ _ _ _ _ inputRun (Command.Runs.seq _ _ _ _ _ _ _ sizeRun after))
    refine ⟨3*n+1+(inputTicks+1+(sizeTicks+1+(1+(parseTicks+1+lastTicks)))),?_,result,?_,?_⟩
    · change _ ≤ commandBudget n target label bits
      dsimp only [commandBudget]
      change inputTicks ≤ inputRoutine.cost (indexed n target label).store at inputCost
      change sizeTicks ≤ sizeTest.cost (preparedStore n target label) at sizeCost
      change parseTicks ≤ parse.cost (sized n target label).store at parseCost
      omega
    · simpa only [command,loaded,Nat.sub_zero] using run
    · rw [saved] at outcome
      exact outcome.trans (labelOutcome_eq_value bound formula valid n equal label bits)
  · have drain : Command.drain.Runs n bits (sized n target label) bits.length .exhausted := by
      simpa only [sized,prepared,Nat.sub_zero] using Command.Runs.drain (n := n) (bits := bits) (sized n target label)
    have after : afterSize.Runs n bits (sized n target label) (1+bits.length) .exhausted := by
      apply Command.Runs.branch
      simpa only [observe,flag,decide_eq_false equal,Bool.false_eq_true,ite_false] using drain
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun
      (Command.Runs.seq _ _ _ _ _ _ _ inputRun (Command.Runs.seq _ _ _ _ _ _ _ sizeRun after))
    refine ⟨3*n+1+(inputTicks+1+(sizeTicks+1+(1+bits.length))),?_,.exhausted,?_,?_⟩
    · change _ ≤ commandBudget n target label bits
      dsimp only [commandBudget]
      change inputTicks ≤ inputRoutine.cost (indexed n target label).store at inputCost
      change sizeTicks ≤ sizeTest.cost (preparedStore n target label) at sizeCost
      omega
    · simpa only [command,loaded,Nat.sub_zero] using run
    · change Outcome.exhausted = valueOutcome (value n target label bits)
      simp only [value,equal,ite_false,valueOutcome]

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
