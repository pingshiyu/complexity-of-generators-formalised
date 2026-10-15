import ComplexityOfGenerators.Simulation.StackSpace.ReadField
import ComplexityOfGenerators.Simulation.StackSpace.MapTransfer

/-! Copy a delimited field, preserving the source and consuming all scratch
space. Source and target may coincide, which pushes a child field immediately
above its parent. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

theorem copy_field (P : Q → Stmt S Q (V × Option S) k)
    (source target register scratch : Fin (k + 1))
    (sr : source ≠ register) (st : source ≠ scratch) (rt : register ≠ scratch)
    (tr : target ≠ register)
    (read mark copy restore store transfer exit : Q)
    (delimiter : S) (keep : S → Bool) (map : S → S)
    (readTable : P read = transferCode source register read mark keep)
    (markTable : P mark = .push source (fun _ => delimiter) (.goto fun _ => copy))
    (copyTable : P copy = duplicateCode register scratch source copy restore)
    (restoreTable : P restore = transferCode scratch register restore store (fun _ => true))
    (storeTable : P store = .push target (fun _ => delimiter) (.goto fun _ => transfer))
    (transferTable : P transfer = mapTransferCode register target transfer exit map)
    (v : V) (stk : Fin (k + 1) → List S) (word suffix : List S)
    (head : stk source = word ++ delimiter :: suffix)
    (more : ∀ s ∈ word, keep s = true) (stop : keep delimiter = false)
    (registerEmpty : stk register = []) (scratchEmpty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : word.length + 1 + (stk target).length ≤ r) :
    Trace P r (localConfig read v stk)
      (localConfig exit v (Function.update stk target (word.map map ++ delimiter :: stk target))) := by
  have first := read_field P source register scratch sr st rt read mark copy restore store
    delimiter keep readTable markTable copyTable restoreTable v stk word suffix head more stop
    registerEmpty scratchEmpty r bound
  let loaded := Function.update stk register word.reverse
  have last := push_field P register target tr.symm transfer exit map store delimiter storeTable
    transferTable v loaded word (by simp [loaded]) r first.end_bound (by
      simpa only [loaded, Function.update_of_ne tr] using room)
  have finish : replaceTwo loaded register target [] (word.map map ++ delimiter :: loaded target) =
      Function.update stk target (word.map map ++ delimiter :: stk target) := by
    simp only [loaded, Function.update_of_ne tr, replaceTwo, Function.update_idem]
    rw [← registerEmpty, Function.update_eq_self]
  rw [finish] at last
  exact first.trans last

end ComplexityOfGenerators.Simulation.StackSpace
