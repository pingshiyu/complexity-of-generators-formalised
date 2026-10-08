import ComplexityOfGenerators.Simulation.OutputEncoding

/-! Output values survive Mathlib's recursive-program, stack-machine and Post
simulations. We retain the final tape projection, rather than reducing all
three simulations to a statement about halting alone. -/

namespace ComplexityOfGenerators.Simulation

open Turing ToPartrec Encodable

set_option backward.isDefEq.respectTransparency false

abbrev RecursiveStackControl := TM2to1.Λ' PartrecToTM2.K'
  (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ' (Option PartrecToTM2.Γ')

def recursiveStackProgram : RecursiveStackControl →
    TM1.Stmt RecursiveAlphabet RecursiveStackControl (Option PartrecToTM2.Γ') :=
  TM2to1.tr PartrecToTM2.tr

def recursiveStackStart (code : Code) (input : List ℕ) :
    TM1.Cfg RecursiveAlphabet RecursiveStackControl (Option PartrecToTM2.Γ') :=
  ⟨some (.normal (PartrecToTM2.trNormal code .halt)), none, Tape.mk₁ (recursiveInput input)⟩

def recursivePostStart (code : Code) (input : List ℕ) :=
  TM1to0.trCfg recursiveStackProgram (recursiveStackStart code input)

theorem recursiveStackStart_related (code : Code) (input : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.init code input) (recursiveStackStart code input) := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  have initial : TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input) =
      PartrecToTM2.init code input := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp
  have relation := TM2to1.trCfg_init
    (Γ := fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
    (Λ := PartrecToTM2.Λ') (σ := Option PartrecToTM2.Γ')
    PartrecToTM2.K'.main (PartrecToTM2.trList input)
  rw [initial] at relation
  exact relation

/-- A computed word reaches a halting Post configuration whose main stack,
scanned rightward from its current head, is exactly the native output encoding.
This statement permits other stacks and work cells to contain irrelevant data. -/
theorem recursive_code_output_tape {α : Type} [Encodable α] (code : Code)
    (input : List ℕ) (word : List α)
    (computed : code.eval input = Part.some (word.reverse.map encode)) :
    ∃ last, last ∈ StateTransition.eval (TM0.step (TM1to0.tr recursiveStackProgram))
        (recursivePostStart code input) ∧
      ∀ n : ℕ, (last.Tape.nth (n : ℤ)).2 PartrecToTM2.K'.main = (outputCells word)[n]? := by
  have stackResult : PartrecToTM2.halt (word.reverse.map encode) ∈
      StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init code input) := by
    rw [PartrecToTM2.tr_eval, computed]
    simp
  obtain ⟨stackLast, stackRelated, stackEvaluation⟩ := StateTransition.tr_eval
    (TM2to1.tr_respects PartrecToTM2.tr) (recursiveStackStart_related code input) stackResult
  obtain ⟨postLast, postRelated, postEvaluation⟩ := StateTransition.tr_eval
    (TM1to0.tr_respects recursiveStackProgram) (show
      TM1to0.trCfg recursiveStackProgram (recursiveStackStart code input) =
        recursivePostStart code input from rfl) stackEvaluation
  refine ⟨postLast, postEvaluation, ?_⟩
  rw [← postRelated]
  cases stackRelated with
  | mk tape projection =>
      intro n
      simp only [TM1to0.trCfg, Tape.mk'_nth_nat, TM2to1.addBottom_nth_snd]
      have main := TM2to1.stk_nth_val n (projection PartrecToTM2.K'.main)
      simpa only [PartrecToTM2.K'.elim, outputCells_encoding] using main

end ComplexityOfGenerators.Simulation
