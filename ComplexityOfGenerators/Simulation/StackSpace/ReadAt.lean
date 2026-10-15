import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Read a stack at a unary position. This is used on a copy of the persistent
input when checking a configuration's input-head observation. The routine is
uniform in the input and position and never increases a stack's length. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def readAtCode (source counter : Fin (k + 1)) (loop inspect : Q) :
    Stmt S Q (V × Option S) k :=
  .peek counter (fun v s => (v.1, s))
    (.branch (fun v => v.2.isSome)
      (.pop counter (fun v _ => v) (.pop source (fun v _ => v)
        (.load (fun v => (v.1, none)) (.goto fun _ => loop))))
      (.load (fun v => (v.1, none)) (.goto fun _ => inspect)))

def inspectCode (source : Fin (k + 1)) (observe : Option S → V → V) (done : Q) :
    Stmt S Q (V × Option S) k :=
  .peek source (fun v s => (observe s v.1, none)) (.goto fun _ => done)

variable (P : Q → Stmt S Q (V × Option S) k) (source counter : Fin (k + 1))
    (different : source ≠ counter) (loop inspect : Q)
    (table : P loop = readAtCode source counter loop inspect)

include table different in
/-- The position counter is consumed and the source loses exactly that many
symbols, with saturating `drop` when the position is beyond the input. -/
theorem readAt_scan (v : V) (stk : Fin (k + 1) → List S) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig inspect v (replaceTwo stk source counter
        ((stk source).drop (stk counter).length) [])) := by
  generalize counterValue : stk counter = count at *
  induction count generalizing stk with
  | nil =>
      have layout : replaceTwo stk source counter (stk source) [] = stk := by
        rw [← counterValue]; exact replaceTwo_same stk source counter
      simpa only [List.length_nil, List.drop_zero, layout] using
        Trace.step (show Within r (localConfig loop v stk) from bound)
          (show TM2.step P (localConfig loop v stk) = some (localConfig inspect v stk) by
            simp [TM2.step, localConfig, table, readAtCode, TM2.stepAux, counterValue])
          (.refl _ bound)
  | cons a count ih =>
      let middle := replaceTwo stk source counter (stk source).tail count
      have midBound : ∀ j, (middle j).length ≤ r := by
        apply replaceTwo_bound stk source counter r bound
        · have h := bound source; simp only [List.length_tail]; omega
        · have h := bound counter; rw [counterValue] at h; simp only [List.length_cons] at h; omega
      have rest := ih middle midBound (replaceTwo_get_dst stk source counter _ _)
      have first : TM2.step P (localConfig loop v stk) = some (localConfig loop v middle) := by
        simp [TM2.step, localConfig, table, readAtCode, TM2.stepAux, counterValue,
          middle, replaceTwo, Function.update_of_ne different]
        funext j
        by_cases hs : j = source <;> by_cases hc : j = counter <;>
          simp_all [Function.update_apply]
      have layout : replaceTwo middle source counter ((middle source).drop count.length) [] =
          replaceTwo stk source counter ((stk source).drop (a :: count).length) [] := by
        simp only [middle, replaceTwo_get_src stk source counter different,
          replaceTwo_replace stk source counter different, List.drop_tail, List.length_cons]
      rw [layout] at rest
      exact .step bound first rest

include table different in
/-- The observed symbol is precisely the head of the suffix at the requested
position, and every unselected stack is preserved. -/
theorem readAt_trace (done : Q) (observe : Option S → V → V)
    (inspectTable : P inspect = inspectCode source observe done)
    (v : V) (stk : Fin (k + 1) → List S) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig loop v stk)
      (localConfig done (observe ((stk source).drop (stk counter).length).head? v)
        (replaceTwo stk source counter ((stk source).drop (stk counter).length) [])) := by
  have scan := readAt_scan P source counter different loop inspect table v stk r bound
  have next : TM2.step P (localConfig inspect v
      (replaceTwo stk source counter ((stk source).drop (stk counter).length) [])) =
      some (localConfig done (observe ((stk source).drop (stk counter).length).head? v)
        (replaceTwo stk source counter ((stk source).drop (stk counter).length) [])) := by
    simp [TM2.step, localConfig, inspectTable, inspectCode, TM2.stepAux,
      replaceTwo_get_src stk source counter different]
  exact scan.trans (.step scan.end_bound next (.refl _ scan.end_bound))

end ComplexityOfGenerators.Simulation.StackSpace
