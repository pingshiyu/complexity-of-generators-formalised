import ComplexityOfGenerators.Simulation.StackSpace.Clear

/-! Clear the six graph-test caches after either a successful or a rejected
query. The input and endpoint column are preserved; the result in finite
control is unchanged. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ClearCaches

open Turing StackSpace
set_option backward.isDefEq.respectTransparency false
variable {S V : Type}

abbrev Label := Fin 7

def program (q : Label) : Stmt S Label (V × Option S) 7 :=
  if h : q.val < 6 then
    clearCode ⟨q.val, by omega⟩ q ⟨q.val + 1, by omega⟩ (fun _ => true)
  else .halt

def memory (stk : Fin 8 → List S) (count : ℕ) : Fin 8 → List S :=
  fun j => if j.val < count then [] else stk j

private theorem prefix_run (v : V) (stk : Fin 8 → List S) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) (count : ℕ) (hc : count ≤ 6) :
    Trace program r (localConfig (0 : Label) v stk)
      (localConfig ⟨count, by omega⟩ v (memory stk count)) := by
  induction count with
  | zero =>
      have zeroMemory : memory stk 0 = stk := by funext j; simp [memory]
      rw [zeroMemory]
      exact .refl _ bound
  | succ count ih =>
      have first := ih (by omega)
      have next := clear_all program (⟨count, by omega⟩ : Fin 8)
        (⟨count, by omega⟩ : Label) (⟨count + 1, by omega⟩ : Label) (fun _ => true)
        (by simp [program, show count < 6 by omega]) v (memory stk count) (by simp) r first.end_bound
      have layout : Function.update (memory stk count) (⟨count, by omega⟩ : Fin 8) [] = memory stk (count + 1) := by
        funext j
        by_cases same : j.val = count
        · have eq : j = (⟨count, by omega⟩ : Fin 8) := Fin.ext same
          simp [eq, memory]
        · have eq : j ≠ (⟨count, by omega⟩ : Fin 8) := fun h => same (congrArg Fin.val h)
          simp only [Function.update_of_ne eq, memory]
          by_cases less : j.val < count <;> simp [less, show (j.val < count + 1) ↔ j.val < count by omega]
      rw [layout] at next
      exact first.trans next

/-- Full cache cleanup is bounded by the incoming radius; no register grows. -/
theorem run (v : V) (stk : Fin 8 → List S) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace program r (localConfig (0 : Label) v stk) (localConfig (6 : Label) v (memory stk 6)) :=
  prefix_run v stk r bound 6 (by omega)

@[simp] theorem memory_input (stk : Fin 8 → List S) : memory stk 6 6 = stk 6 := rfl
@[simp] theorem memory_column (stk : Fin 8 → List S) : memory stk 6 7 = stk 7 := rfl

end ComplexityOfGenerators.Simulation.SavitchMachine.ClearCaches
