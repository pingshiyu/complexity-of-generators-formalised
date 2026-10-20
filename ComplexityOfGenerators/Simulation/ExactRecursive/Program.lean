import ComplexityOfGenerators.Simulation.ExactRecursive.Frame
import ComplexityOfGenerators.Simulation.WordStack.LengthTest
import ComplexityOfGenerators.Simulation.WordStack.RandomInput
import ComplexityOfGenerators.Simulation.WordStack.Output

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def lengthSlots : LengthTest.Layout 35 where
  toFun | 0 => 11 | 1 => 13 | 2 => 30 | 3 => 31 | 4 => 32 | 5 => 33
  inj' := by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem lengthSlots_apply (i : Fin 6) :
    lengthSlots i = match i with | 0 => 11 | 1 => 13 | 2 => 30 | 3 => 31 | 4 => 32 | 5 => 33 := rfl

def lengthTest : Controller B V := LengthTest.routine lengthSlots .unit

theorem lengthTest_fixes_clock : (lengthTest B V).Fixes 22 := by
  intro s
  simp [lengthTest, LengthTest.routine_eval]

def searchSetup (count : PolynomialBound) : Controller B V :=
  (WordStack.Routine.clear 12).seq
  ((WordStack.Routine.clear 25).seq
  ((flag B V 26 false).seq
  ((flag B V 27 false).seq (counter B V 23 (by decide) count))))

def searchFinish : Controller B V :=
  WordStack.Routine.branch 27 fun found => if found.isSome then
    WordStack.Routine.assign 25 11 33 (by decide) (by decide) (by decide) id
  else WordStack.Routine.branch 30 fun target =>
    if target.isSome then flag B V 28 true else flag B V 29 false

noncomputable def search (first : α) (count seed time : PolynomialBound) : Controller B V :=
  (searchSetup B V count).seq
  ((WordStack.Routine.iterate 23 (searchStep B V first seed time)
    (searchStep_fixes B V first seed time 23 (Or.inr rfl))).seq (searchFinish B V))

theorem searchSetup_fixes_clock (count : PolynomialBound) : (searchSetup B V count).Fixes 22 :=
  (WordStack.Routine.fixes_clear 12 22 (by decide)).seq
  ((WordStack.Routine.fixes_clear 25 22 (by decide)).seq
  ((flag_fixes B V 26 22 false (by decide)).seq
  ((flag_fixes B V 27 22 false (by decide)).seq
    (counter_fixes B V 23 (by decide) count 22 (by decide) (by decide) (by decide) (by decide)))))

theorem searchFinish_fixes_clock : (searchFinish B V).Fixes 22 := by
  apply WordStack.Routine.Fixes.branch
  intro found
  split
  · exact WordStack.Routine.fixes_assign 25 11 33 (by decide) (by decide) (by decide) id 22 (by decide) (by decide)
  · apply WordStack.Routine.Fixes.branch
    intro target
    split
    · exact flag_fixes B V 28 22 true (by decide)
    · exact flag_fixes B V 29 22 false (by decide)

theorem search_fixes_clock (first : α) (count seed time : PolynomialBound) :
    (search B V first count seed time).Fixes 22 :=
  (searchSetup_fixes_clock B V count).seq
  ((WordStack.Routine.Fixes.iterate 23 (searchStep B V first seed time)
    (searchStep_fixes B V first seed time 23 (Or.inr rfl)) 22 (by decide)
    (searchStep_fixes B V first seed time 22 (Or.inl rfl))).seq (searchFinish_fixes_clock B V))

/-- The successful stopping offer is optional, including at the first word
whose length already equals the target. -/
noncomputable def stopOffer (first : α) (count seed time : PolynomialBound) : Controller B V :=
  WordStack.Routine.branch 30 fun target =>
    if target.isSome then flag B V 28 true else search B V first count seed time

noncomputable def walkStep (first : α) (count seed time : PolynomialBound) : Controller B V :=
  WordStack.Routine.branch 29 fun valid => if valid.isNone then WordStack.Routine.skip else
  WordStack.Routine.branch 28 fun stopped => if stopped.isSome then WordStack.Routine.skip else
    (lengthTest B V).seq (coin B V (search B V first count seed time) (stopOffer B V first count seed time))

theorem walkStep_fixes_clock (first : α) (count seed time : PolynomialBound) :
    (walkStep B V first count seed time).Fixes 22 := by
  apply WordStack.Routine.Fixes.branch
  intro valid
  split
  · exact WordStack.Routine.fixes_skip 22
  · apply WordStack.Routine.Fixes.branch
    intro stopped
    split
    · exact WordStack.Routine.fixes_skip 22
    · apply WordStack.Routine.Fixes.seq (lengthTest_fixes_clock B V)
      apply coin_fixes B V _ _ 22 (by decide) (search_fixes_clock B V first count seed time)
      apply WordStack.Routine.Fixes.branch
      intro target
      split
      · exact flag_fixes B V 28 22 true (by decide)
      · exact search_fixes_clock B V first count seed time

def baseFinish : Controller B V :=
  WordStack.Routine.branch 0 fun status => match status with
    | some (.base (.state .accepted)) =>
      (takeOutput B V 11 (by decide) (baseOutput B V)).seq (flag B V 29 true)
    | _ => flag B V 29 false

noncomputable def body (first : α) (baseSeed baseTime inverseSeed inverseTime count fuel : PolynomialBound) :
    Controller B V :=
  (baseTrial B V baseSeed baseTime).seq
  ((baseFinish B V).seq
  ((counter B V 22 (by decide) fuel).seq
  ((WordStack.Routine.iterate 22 (walkStep B V first count inverseSeed inverseTime)
    (walkStep_fixes_clock B V first count inverseSeed inverseTime)).seq (lengthTest B V))))

def outputLetter : Cell B V → Option α
  | .letter a => some a
  | _ => none

def finish : Command (Cell B V) α 35 :=
  .branch 29 fun valid => if valid.1.isSome then
    .branch 30 fun target => if target.1.isSome then Command.emitWord 11 (outputLetter B V) else .drain
  else .drain

def prepareCommand (seed : PolynomialBound) : Command (Cell B V) α 35 :=
  (Command.loadIndex 13 Symbol.unit).seq
  ((counter B V 18 (by decide) seed).command.seq
  ((Command.collect 18 34 Symbol.bit).seq
    (Command.transfer 34 17 id)))

/-- One fixed finite command, uniformly parameterised by the unary index.
All random bits are collected before the deterministic controller starts. -/
noncomputable def command (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) : Command (Cell B V) α 35 :=
  (prepareCommand B V seed).seq
    ((body B V first baseSeed baseTime inverseSeed inverseTime count fuel).command.seq (finish B V))

end ComplexityOfGenerators.Simulation.ExactRecursive
