import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Fixed literals in finite stack programs. The literal length is part of
the program text; source-step and native compiler bounds both include it. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def pushCopies (register : Fin (k + 1)) (symbol : S) : ℕ → Stmt S Q V k → Stmt S Q V k
  | 0, code => code
  | n + 1, code => .push register (fun _ => symbol) (pushCopies register symbol n code)

theorem pushCopies_stepAux (register : Fin (k + 1)) (symbol : S) (n : ℕ)
    (code : Stmt S Q V k) (v : V) (stk : Fin (k + 1) → List S) :
    TM2.stepAux (pushCopies register symbol n code) v stk =
      TM2.stepAux code v (Function.update stk register (List.replicate n symbol ++ stk register)) := by
  induction n generalizing stk with
  | zero => simp [pushCopies, Function.update_eq_self]
  | succ n ih =>
      simp only [pushCopies, TM2.stepAux, ih, Function.update_self, Function.update_idem,
        List.replicate_succ', List.append_assoc, List.singleton_append]

/-- Push a fixed literal in traversal order, leaving it reversed on the
stack. The literal is fixed when the finite program is constructed. -/
def pushLiteral (register : Fin (k + 1)) : List S → Stmt S Q V k → Stmt S Q V k
  | [], code => code
  | a :: rest, code => .push register (fun _ => a) (pushLiteral register rest code)

theorem pushLiteral_stepAux (register : Fin (k + 1)) (word : List S)
    (code : Stmt S Q V k) (v : V) (stk : Fin (k + 1) → List S) :
    TM2.stepAux (pushLiteral register word code) v stk =
      TM2.stepAux code v (Function.update stk register (word.reverse ++ stk register)) := by
  induction word generalizing stk with
  | nil => simp [pushLiteral, Function.update_eq_self]
  | cons a word ih =>
      simp only [pushLiteral, TM2.stepAux, ih, Function.update_self, Function.update_idem,
        List.reverse_cons, List.append_assoc, List.singleton_append]

end ComplexityOfGenerators.Simulation.StackSpace
