import ComplexityOfGenerators.Simulation.FiniteResults
import ComplexityOfGenerators.Simulation.RecursiveResult

/-! The established recursive-program compiler, restricted to finite control,
with an interface specifying the output cells of the final tape. -/

namespace ComplexityOfGenerators.Simulation

open Turing ToPartrec Encodable

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The library supplies finite support at each compilation stage. The chosen
initial label is the entry point of this particular recursive program. -/
def recursivePostImplementation (code : Code) :
    letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
    FinitePostImplementation (TM1to0.tr recursiveStackProgram) := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  exact finitePostImplementation (TM1to0.tr recursiveStackProgram)
    (TM1to0.trStmts recursiveStackProgram (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp code .halt)))
    (TM1to0.tr_supports recursiveStackProgram (TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports code .halt)))

/-- A computed word remains on the final main stack after restriction to a
finite set of control states. This includes the correct native entry label. -/
theorem recursivePostImplementation_result {α : Type} [Encodable α]
    (code : Code) (input : List ℕ) (word : List α)
    (computed : code.eval input = Part.some (word.reverse.map encode)) :
    letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
    let impl := recursivePostImplementation code
    let := impl.initialControl
    ∃ last, last ∈ StateTransition.eval (TM0.step impl.machine) (TM0.init (recursiveInput input)) ∧
      ∀ n : ℕ, (last.Tape.nth (n : ℤ)).2 PartrecToTM2.K'.main = (outputCells word)[n]? := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  let impl := recursivePostImplementation code
  let := impl.initialControl
  obtain ⟨last, evaluated, decoded⟩ := recursive_code_output_tape code input word computed
  have initial : recursivePostStart code input =
      (TM0.init (recursiveInput input) : TM0.Cfg RecursiveAlphabet (TM1to0.Λ' recursiveStackProgram)) := rfl
  rw [initial] at evaluated
  obtain ⟨final, result, tape⟩ := impl.result_correct (recursiveInput input) last evaluated
  exact ⟨final, result, fun n => by rw [tape]; exact decoded n⟩

end

end ComplexityOfGenerators.Simulation
