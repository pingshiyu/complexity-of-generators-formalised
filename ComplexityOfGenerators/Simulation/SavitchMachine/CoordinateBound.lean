import ComplexityOfGenerators.Simulation.SavitchMachine.Ruler
import ComplexityOfGenerators.Simulation.StackSpace.Embed
import ComplexityOfGenerators.Simulation.StackSpace.Expand
import ComplexityOfGenerators.Simulation.StackSpace.Clear

/-! Construct the dynamic coordinate bounds used by the graph tester. The
finite program preserves the configuration bitstream and original input, and
returns either `n+1` or `2*space(n)+1` in the designated unary bound register. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateBound

open Turing StackSpace
set_option backward.isDefEq.respectTransparency false
variable {S V : Type} [Inhabited S]

inductive Label (degree : ℕ)
  | ruler (pc : Ruler.Label degree) | clearValue | clearFactor | double | seed | done
  deriving DecidableEq, Fintype

def slots : Fin 5 ↪ Fin 7 := ⟨![6, 1, 2, 3, 4], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def program (symbol : S) (space : PolynomialBound) (work : Bool) :
    Label space.degree → Stmt S (Label space.degree) (V × Option S) 6
  | .ruler .finish => .goto fun _ => if work then .clearFactor else .clearValue
  | .ruler pc => embedCode slots Label.ruler (Ruler.program symbol space pc)
  | .clearValue => clearCode 1 .clearValue .done (fun _ => true)
  | .clearFactor => clearCode 2 .clearFactor .double (fun _ => true)
  | .double => expandCode 1 2 symbol 2 .double .seed
  | .seed => .push 2 (fun _ => symbol) (.goto fun _ => .done)
  | .done => .halt

def registers (symbol : S) (source input : List S) (bound : ℕ) : Fin 7 → List S :=
  ![source, [], List.replicate bound symbol, [], [], [], input]

/-- Both kinds of coordinate ruler are built uniformly by finite control.
The existing polynomial stack bound covers their construction, including the
factor register used for constant space polynomials. -/
theorem run (symbol : S) (space : PolynomialBound) (work : Bool) (v : V)
    (source input : List S) (r : ℕ) (sourceRoom : source.length ≤ r)
    (rulerRoom : input.length + space input.length + 1 ≤ r)
    (workRoom : 2 * space input.length + 1 ≤ r) :
    Trace (program symbol space work) r
      (localConfig (.ruler .copyInput) v (registers symbol source input 0))
      (localConfig .done v (registers symbol source input
        (if work then 2 * space input.length + 1 else input.length + 1))) := by
  let P := program (V := V) symbol space work
  let original := registers symbol source input 0
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, registers] <;> omega
  have ruled := ((Ruler.run_with symbol space v input).mono rulerRoom).embed_active
    (by simp [localConfig]) slots Label.ruler P
    (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) original initial
  let prepared : Fin 7 → List S :=
    ![source, List.replicate (space input.length) symbol, List.replicate (input.length + 1) symbol, [], [], [], input]
  have firstLayout : Function.extend slots ![input, [], [], [], []] original = original := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside; rfl
  have lastLayout : Function.extend slots
      ![input, List.replicate (space input.length) symbol, List.replicate (input.length + 1) symbol, [], []]
      original = prepared := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside
      fin_cases j <;> simp_all [slots, Fin.exists_fin_succ, original, registers, prepared]
  simp only [embedConfig, localConfig, Option.map_some, firstLayout, lastLayout] at ruled
  cases work with
  | false =>
      have cleared := clear_all P 1 .clearValue .done (fun _ => true) rfl v prepared (by simp) r ruled.end_bound
      have layout : Function.update prepared (1 : Fin 7) [] = registers symbol source input (input.length + 1) := by
        funext j; fin_cases j <;> simp [prepared, registers]
      rw [layout] at cleared
      exact ruled.trans (.step ruled.end_bound rfl cleared)
  | true =>
      have cleared := clear_all P 2 .clearFactor .double (fun _ => true) rfl v prepared (by simp) r ruled.end_bound
      let withSpace : Fin 7 → List S := ![source, List.replicate (space input.length) symbol, [], [], [], [], input]
      have clearLayout : Function.update prepared (2 : Fin 7) [] = withSpace := by
        funext j; fin_cases j <;> simp [prepared, withSpace]
      rw [clearLayout] at cleared
      have doubled := expand_all P 1 2 (by decide) symbol 2 .double .seed rfl v withSpace r
        cleared.end_bound (by simp [withSpace]; omega)
      have doubleLayout : replaceTwo withSpace (1 : Fin 7) 2 []
          (List.replicate (2 * (withSpace 1).length) symbol ++ withSpace 2) =
          registers symbol source input (2 * space input.length) := by
        funext j; fin_cases j <;> simp [withSpace, registers, replaceTwo]
      rw [doubleLayout] at doubled
      have last : TM2.step P (localConfig .seed v (registers symbol source input (2 * space input.length))) =
          some (localConfig .done v (registers symbol source input (2 * space input.length + 1))) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, registers, List.replicate_succ]
        funext j; fin_cases j <;> simp
      have finalBound : ∀ j, (registers symbol source input (2 * space input.length + 1) j).length ≤ r := by
        intro j; fin_cases j <;> simp [registers] <;> omega
      exact ruled.trans (.step ruled.end_bound rfl
        (cleared.trans (doubled.trans (.step doubled.end_bound last (.refl _ finalBound)))))

end ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateBound
