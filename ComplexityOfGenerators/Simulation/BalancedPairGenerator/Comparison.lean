import ComplexityOfGenerators.Simulation.UnionGenerator.Views
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

abbrev Cell := UnionGenerator.Cell G G
abbrev Store := Local.Store (Cell G) 35
abbrev Controller := WordStack.Routine (Cell G) α 35

def comparisonSlots (first second flag : Fin 35)
    (distinct : first ≠ second ∧ first ≠ flag ∧ second ≠ flag)
    (outside : 3 ≤ first.val ∧ 3 ≤ second.val ∧ 3 ≤ flag.val) : Fin 6 ↪ Fin 35 where
  toFun | 0 => first | 1 => second | 2 => flag | 3 => 0 | 4 => 1 | 5 => 2
  inj' := by
    intro i j equal
    fin_cases i <;> fin_cases j <;> simp_all [ne_comm] <;> omega

@[simp] theorem comparisonSlots_apply (first second flag : Fin 35) (distinct outside) (i : Fin 6) :
    comparisonSlots first second flag distinct outside i = match i with
      | 0 => first | 1 => second | 2 => flag | 3 => 0 | 4 => 1 | 5 => 2 := rfl

def equalLeft : Controller G :=
  LengthTest.routine (comparisonSlots 25 22 23 (by decide) (by decide)) .unit

def equalRight : Controller G :=
  LengthTest.routine (comparisonSlots 26 22 24 (by decide) (by decide)) .unit

def leftBelow : Controller G :=
  RationalSelection.Compare.routine (comparisonSlots 22 25 23 (by decide) (by decide)) .unit

def rightAbove : Controller G :=
  RationalSelection.Compare.routine (comparisonSlots 26 22 24 (by decide) (by decide)) .unit

def rightBelow : Controller G :=
  RationalSelection.Compare.routine (comparisonSlots 22 26 23 (by decide) (by decide)) .unit

def leftAbove : Controller G :=
  RationalSelection.Compare.routine (comparisonSlots 25 22 24 (by decide) (by decide)) .unit

def pick (word : Fin 35) (different : word ≠ 31 ∧ word ≠ 33) : Controller G :=
  (WordStack.Routine.assign word 31 33 different.1 different.2 (by decide) id).seq
    (UnionGenerator.flag G G 32 true)

theorem pick_eval (word : Fin 35) (different : word ≠ 31 ∧ word ≠ 33) (s : Store G) :
    (pick G word different).eval s = Function.update (Function.update
      (Function.update s 33 []) 31 (s word)) 32 [Symbol.unit] := by
  simp [pick, WordStack.Routine.seq, WordStack.Routine.assign_eval, UnionGenerator.flag_eval,
    UnionGenerator.flagWord, different.1]

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
