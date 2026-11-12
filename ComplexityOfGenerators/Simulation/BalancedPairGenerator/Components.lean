import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Comparison
import ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection.Basic
import ComplexityOfGenerators.Foundations.BalancedPairPhase

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

def decodeBit : Cell G → Bool
  | .bit value => value
  | _ => false

noncomputable def select (low high : Fin 35) (lowSafe : PreparedRationalSelection.Safe low)
    (highSafe : PreparedRationalSelection.Safe high) : Controller G :=
  PreparedRationalSelection.routine Symbol.bit (decodeBit G) (fun _ => rfl) low high lowSafe highSafe

def selectionFinish (low high : Fin 35) (lowDifferent : low ≠ 31 ∧ low ≠ 33)
    (highDifferent : high ≠ 31 ∧ high ≠ 33) : Controller G :=
  WordStack.Routine.branch 12 fun valid => if valid.isSome then
    WordStack.Routine.branch 13 fun choice => if choice.isSome then
      pick G low lowDifferent else pick G high highDifferent
  else WordStack.Routine.skip

noncomputable def weightedLeft : Controller G :=
  (select G 25 26 (by decide) (by decide)).seq
    (selectionFinish G 25 26 (by decide) (by decide))

noncomputable def weightedRight : Controller G :=
  (select G 26 25 (by decide) (by decide)).seq
    (selectionFinish G 26 25 (by decide) (by decide))

def both (first second : Fin 35) (yes no : Controller G) : Controller G :=
  WordStack.Routine.branch first fun left => if left.isSome then
    WordStack.Routine.branch second fun right => if right.isSome then yes else no
  else no

noncomputable def reverseCase : Controller G :=
  (rightBelow G).seq ((leftAbove G).seq (both G 23 24 (weightedRight G) WordStack.Routine.skip))

noncomputable def strictCases : Controller G :=
  (leftBelow G).seq ((rightAbove G).seq (both G 23 24 (weightedLeft G) (reverseCase G)))

noncomputable def equalCase : Controller G :=
  (equalLeft G).seq ((equalRight G).seq (both G 23 24 (pick G 25 (by decide)) (strictCases G)))

noncomputable def classify : Controller G :=
  both G 27 28 (equalCase G) WordStack.Routine.skip

def reset : Controller G :=
  (WordStack.Routine.clear 11).seq
  ((WordStack.Routine.clear 12).seq
  ((WordStack.Routine.clear 14).seq
  ((WordStack.Routine.clear 25).seq
  ((WordStack.Routine.clear 26).seq
  ((UnionGenerator.flag G G 27 false).seq
  ((UnionGenerator.flag G G 28 false).seq
  ((WordStack.Routine.clear 31).seq (UnionGenerator.flag G G 32 false))))))))

noncomputable def calls (seed time : PolynomialBound) : Controller G :=
  (reset G).seq
  ((UnionGenerator.leftTrial G G seed time).seq
  ((UnionGenerator.leftFinish G G).seq
  ((UnionGenerator.rightTrial G G seed time).seq (UnionGenerator.rightFinish G G))))

noncomputable def phase (seed time : PolynomialBound) : Controller G :=
  (calls G seed time).seq (classify G)

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
