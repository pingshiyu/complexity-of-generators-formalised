import ComplexityOfGenerators.Simulation.StackSpace.ReadField

/-! Read an endpoint from a Savitch frame column without consuming that frame.
The original delimiter and suspended parent frames are restored. The previously
decoded coordinate, coordinate bound and persistent input remain available. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Endpoint

open Turing StackSpace
set_option backward.isDefEq.respectTransparency false
variable {S V : Type} [Inhabited S]

inductive Label | load | mark | copy | restore | forward | done
  deriving DecidableEq, Fintype

def program (delimiter : S) (keep : S → Bool) : Label → Stmt S Label (V × Option S) 7
  | .load => transferCode 7 3 .load .mark keep
  | .mark => .push 7 (fun _ => delimiter) (.goto fun _ => .copy)
  | .copy => duplicateCode 3 4 7 .copy .restore
  | .restore => transferCode 4 3 .restore .forward (fun _ => true)
  | .forward => transferCode 3 0 .forward .done (fun _ => true)
  | .done => .halt

/-- Return the endpoint in traversal order in cache zero. Only that cache
changes; the source column and every other register are preserved exactly. -/
theorem run (delimiter : S) (keep : S → Bool) (v : V) (stk : Fin 8 → List S)
    (word suffix : List S) (head : stk 7 = word ++ delimiter :: suffix)
    (more : ∀ s ∈ word, keep s = true) (stop : keep delimiter = false)
    (outputEmpty : stk 0 = []) (registerEmpty : stk 3 = []) (scratchEmpty : stk 4 = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace (program delimiter keep) r (localConfig .load v stk)
      (localConfig .done v (Function.update stk (0 : Fin 8) word)) := by
  let P := program (V := V) delimiter keep
  have loaded := read_field P 7 3 4 (by decide) (by decide) (by decide)
    .load .mark .copy .restore .forward delimiter keep rfl rfl rfl rfl v stk word suffix
    head more stop registerEmpty scratchEmpty r bound
  have forwarded := transfer_all P 3 0 (by decide) .forward .done (fun _ => true) rfl
    v (Function.update stk (3 : Fin 8) word.reverse) (by simp) r loaded.end_bound (by
      have sourceBound := bound 7
      rw [head] at sourceBound
      simp [outputEmpty] at *
      omega)
  have layout : replaceTwo (Function.update stk (3 : Fin 8) word.reverse) 3 0 []
      (((Function.update stk (3 : Fin 8) word.reverse) 3).reverse ++
        (Function.update stk (3 : Fin 8) word.reverse) 0) = Function.update stk (0 : Fin 8) word := by
    funext j
    by_cases atOutput : j = 0 <;> by_cases atRegister : j = 3 <;>
      simp_all [replaceTwo, Function.update_apply]
  rw [layout] at forwarded
  exact loaded.trans forwarded

end ComplexityOfGenerators.Simulation.SavitchMachine.Endpoint
