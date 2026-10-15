import ComplexityOfGenerators.Simulation.StackSpace.Trace

/-! Reuse a stack routine in the presence of one additional persistent stack.
This permits input and ruler data to survive the recursive interpreter. The
new stack is untouched, but its full length is still charged to the bound. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ}

def extendCode : Stmt S Q V k → Stmt S Q V (k + 1)
  | .push j f rest => .push j.castSucc f (extendCode rest)
  | .pop j f rest => .pop j.castSucc f (extendCode rest)
  | .peek j f rest => .peek j.castSucc f (extendCode rest)
  | .load f rest => .load f (extendCode rest)
  | .branch f yes no => .branch f (extendCode yes) (extendCode no)
  | .goto f => .goto f
  | .halt => .halt

def extendConfig (extra : List S) (c : Source S Q V k) : Source S Q V (k + 1) :=
  ⟨c.l, c.var, Fin.snoc c.stk extra⟩

theorem extend_stepAux (code : Stmt S Q V k) (v : V) (stk : Fin (k + 1) → List S)
    (extra : List S) :
    TM2.stepAux (extendCode code) v (Fin.snoc stk extra) =
      extendConfig extra (TM2.stepAux code v stk) := by
  induction code generalizing v stk with
  | push j f rest ih => simpa only [extendCode, TM2.stepAux, Fin.snoc_castSucc, ← Fin.snoc_update] using ih v (Function.update stk j (f v :: stk j))
  | pop j f rest ih => simpa only [extendCode, TM2.stepAux, Fin.snoc_castSucc, ← Fin.snoc_update] using ih (f v (stk j).head?) (Function.update stk j (stk j).tail)
  | peek j f rest ih => simpa only [extendCode, TM2.stepAux, Fin.snoc_castSucc] using ih (f v (stk j).head?) stk
  | load f rest ih => exact ih (f v) stk
  | branch f yes no ihYes ihNo =>
      cases h : f v <;> simp only [extendCode, TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ihNo v stk
      · exact ihYes v stk
  | goto f => rfl
  | halt => rfl

theorem extend_step (P : Q → Stmt S Q V k) (c : Source S Q V k) (extra : List S) :
    TM2.step (fun q => extendCode (P q)) (extendConfig extra c) =
      (TM2.step P c).map (extendConfig extra) := by
  rcases c with ⟨label, v, stk⟩
  cases label <;> simp [TM2.step, extendConfig, extend_stepAux]

theorem extend_bound (c : Source S Q V k) (extra : List S) (r : ℕ)
    (bound : Within r c) (room : extra.length ≤ r) : Within r (extendConfig extra c) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [extendConfig] using room
  · simpa [extendConfig] using bound i

theorem Trace.extend {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (extra : List S) (room : extra.length ≤ r) :
    Trace (fun q => extendCode (P q)) r (extendConfig extra a) (extendConfig extra b) := by
  induction path with
  | refl c bound => exact .refl _ (extend_bound c extra r bound room)
  | step bound next tail ih =>
      exact .step (extend_bound _ extra r bound room) (by rw [extend_step, next]; rfl) ih

theorem step_as_map (P : Q → Stmt S Q V k) (c : Source S Q V k) :
    TM2.step P c = c.l.map (fun q => TM2.stepAux (P q) c.var c.stk) := by
  rcases c with ⟨label, v, stk⟩
  cases label <;> rfl

/-- A program may replace unused halt labels with separately verified
subroutines. A trace ending at an active label cannot execute an earlier halt. -/
theorem Trace.extend_active {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (active : b.l ≠ none)
    (R : Q → Stmt S Q V (k + 1))
    (table : ∀ q, P q ≠ .halt → R q = extendCode (P q))
    (extra : List S) (room : extra.length ≤ r) :
    Trace R r (extendConfig extra a) (extendConfig extra b) := by
  induction path with
  | refl c bound => exact .refl _ (extend_bound c extra r bound room)
  | @step a c b bound next tail ih =>
      have label : ∃ q, a.l = some q := by
        cases h : a.l with
        | none => simp [step_as_map, h] at next
        | some q => exact ⟨q, rfl⟩
      obtain ⟨q, label⟩ := label
      have notHalt : P q ≠ .halt := by
        intro halted
        have child : c.l = none := by
          simp only [step_as_map, label, Option.map_some, halted, TM2.stepAux] at next
          exact congrArg TM2.Cfg.l (Option.some.inj next).symm
        cases tail with
        | refl => exact active child
        | step _ next _ => simp [step_as_map, child] at next
      have step : TM2.step R (extendConfig extra a) = some (extendConfig extra c) := by
        have same : TM2.step R (extendConfig extra a) =
            TM2.step (fun q => extendCode (P q)) (extendConfig extra a) := by
          simp only [step_as_map, extendConfig, label, Option.map_some, table q notHalt]
        rw [same, extend_step, next]
        rfl
      exact .step (extend_bound _ extra r bound room) step (ih active)

end ComplexityOfGenerators.Simulation.StackSpace
