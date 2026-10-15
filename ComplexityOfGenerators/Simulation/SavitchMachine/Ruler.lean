import ComplexityOfGenerators.Simulation.StackSpace.Ruler

/-! A concrete finite program that prepares a polynomial-size unary ruler
from an input stack. It is independent of the input length and preserves the
input. Its exponent and coefficient are fixed parts of the program. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Ruler

open Turing StackSpace
set_option backward.isDefEq.respectTransparency false

inductive Label (degree : ℕ)
  | copyInput | duplicateInput | mapInput | seed
  | scan (stage : Fin degree)
  | copy (stage : Fin degree)
  | duplicate (stage : Fin degree)
  | restore (stage : Fin degree)
  | finish
  deriving DecidableEq, Fintype

variable {S V : Type} [Inhabited S]

def phase (degree i : ℕ) : Label degree :=
  if h : i < degree then .scan ⟨i, h⟩ else .finish

def program (symbol : S) (p : PolynomialBound) : Label p.degree → Stmt S (Label p.degree) (V × Option S) 4
  | .copyInput => transferCode 0 4 .copyInput .duplicateInput (fun _ => true)
  | .duplicateInput => duplicateCode 4 0 1 .duplicateInput .mapInput
  | .mapInput => mapTransferCode 1 2 .mapInput .seed (fun _ => symbol)
  | .seed => .push 2 (fun _ => symbol)
      (pushCopies 1 symbol p.coefficient (.goto fun _ => phase p.degree 0))
  | .scan i => multiplyScan 1 (.copy i) (.restore i)
  | .copy i => transferCode 2 4 (.copy i) (.duplicate i) (fun _ => true)
  | .duplicate i => duplicateCode 4 2 3 (.duplicate i) (phase p.degree i.val)
  | .restore i => transferCode 3 1 (.restore i) (phase p.degree (i.val + 1)) (fun _ => true)
  | .finish => .halt

/-- The bound explicitly includes the preserved input and the factor `n+1`,
also for constant polynomials where those can exceed the polynomial value. -/
theorem run_with (symbol : S) (p : PolynomialBound) (v : V) (word : List S) :
    Trace (program symbol p) (word.length + p word.length + 1)
      (localConfig .copyInput v ![word, [], [], [], []])
      (localConfig .finish v
        ![word, List.replicate (p word.length) symbol, List.replicate (word.length + 1) symbol, [], []]) := by
  have path := polynomial_ruler (program symbol p) (Function.Embedding.refl (Fin 5)) symbol p
    .copyInput .duplicateInput .mapInput .seed (phase p.degree) Label.copy Label.duplicate Label.restore
    rfl rfl rfl rfl
    (fun i => by simp only [phase, i.isLt, ↓reduceDIte, program]; rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    v ![word, [], [], [], []]
    (by intro j nonzero; fin_cases j <;> simp_all)
    (word.length + p word.length + 1)
    (by intro j; fin_cases j <;> simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  have finish : Function.update (Function.update ![word, [], [], [], []] (2 : Fin 5)
      (List.replicate (word.length + 1) symbol)) (1 : Fin 5) (List.replicate (p word.length) symbol) =
      ![word, List.replicate (p word.length) symbol, List.replicate (word.length + 1) symbol, [], []] := by
    funext j
    fin_cases j <;> simp [Function.update_apply]
  simpa only [phase, lt_self_iff_false, ↓reduceDIte, Function.Embedding.refl_apply,
    Matrix.cons_val_zero, finish] using path

theorem run (symbol : S) (p : PolynomialBound) (word : List S) :
    Trace (program symbol p) (word.length + p word.length + 1)
      (localConfig .copyInput () ![word, [], [], [], []])
      (localConfig .finish ()
        ![word, List.replicate (p word.length) symbol, List.replicate (word.length + 1) symbol, [], []]) :=
  run_with symbol p () word

end ComplexityOfGenerators.Simulation.SavitchMachine.Ruler
