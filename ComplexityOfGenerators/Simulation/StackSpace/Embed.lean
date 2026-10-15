import ComplexityOfGenerators.Simulation.StackSpace.Extend
import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Embed a verified routine into a larger finite program. Stack indices and
control labels are renamed; unselected stacks are preserved and charged to
the space bound. A routine's halt label can become its caller's continuation. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q R V : Type} {k l : ℕ}

def embedCode (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R) : Stmt S Q V k → Stmt S R V l
  | .push j f rest => .push (slots j) f (embedCode slots labels rest)
  | .pop j f rest => .pop (slots j) f (embedCode slots labels rest)
  | .peek j f rest => .peek (slots j) f (embedCode slots labels rest)
  | .load f rest => .load f (embedCode slots labels rest)
  | .branch f yes no => .branch f (embedCode slots labels yes) (embedCode slots labels no)
  | .goto f => .goto (labels ∘ f)
  | .halt => .halt

noncomputable def embedConfig (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R)
    (background : Fin (l + 1) → List S) (c : Source S Q V k) : Source S R V l :=
  ⟨c.l.map labels, c.var, Function.extend slots c.stk background⟩

/-- A convenient layout rule for composing separately verified routines. -/
theorem extend_eq (slots : Fin (k + 1) ↪ Fin (l + 1))
    (background target : Fin (l + 1) → List S) (source : Fin (k + 1) → List S)
    (selected : ∀ i, target (slots i) = source i)
    (untouched : ∀ j, (¬ ∃ i, slots i = j) → target j = background j) :
    Function.extend slots source background = target := by
  classical
  funext j
  by_cases inside : ∃ i, slots i = j
  · obtain ⟨i, rfl⟩ := inside
    rw [slots.injective.extend_apply, selected]
  · rw [Function.extend_apply' _ _ _ inside, untouched j inside]


theorem embed_local {W : Type} (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R)
    (background target : Fin (l + 1) → List S) (source : Fin (k + 1) → List S)
    (q : Q) (v : W) (layout : Function.extend slots source background = target) :
    embedConfig slots labels background (localConfig q v source) = localConfig (labels q) v target := by
  simp only [embedConfig, localConfig, Option.map_some]
  rw [layout]


theorem extend_update (slots : Fin (k + 1) ↪ Fin (l + 1))
    (background : Fin (l + 1) → List S) (stk : Fin (k + 1) → List S)
    (j : Fin (k + 1)) (word : List S) :
    Function.extend slots (Function.update stk j word) background =
      Function.update (Function.extend slots stk background) (slots j) word := by
  classical
  funext i
  by_cases inside : ∃ a, slots a = i
  · obtain ⟨a, rfl⟩ := inside
    simp only [slots.injective.extend_apply]
    by_cases same : a = j
    · subst a; simp
    · simp [Function.update_of_ne same, Function.update_of_ne (fun eq => same (slots.injective eq)),
        slots.injective.extend_apply]
  · have different : i ≠ slots j := fun eq => inside ⟨j, eq.symm⟩
    simp [Function.extend_apply' _ _ _ inside, Function.update_of_ne different]

theorem embed_stepAux (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R)
    (background : Fin (l + 1) → List S) (code : Stmt S Q V k) (v : V)
    (stk : Fin (k + 1) → List S) :
    TM2.stepAux (embedCode slots labels code) v (Function.extend slots stk background) =
      embedConfig slots labels background (TM2.stepAux code v stk) := by
  induction code generalizing v stk with
  | push j f rest ih =>
      simpa only [embedCode, TM2.stepAux, slots.injective.extend_apply, ← extend_update]
        using ih v (Function.update stk j (f v :: stk j))
  | pop j f rest ih =>
      simpa only [embedCode, TM2.stepAux, slots.injective.extend_apply, ← extend_update]
        using ih (f v (stk j).head?) (Function.update stk j (stk j).tail)
  | peek j f rest ih =>
      simpa only [embedCode, TM2.stepAux, slots.injective.extend_apply] using ih (f v (stk j).head?) stk
  | load f rest ih => exact ih (f v) stk
  | branch f yes no ihYes ihNo =>
      cases h : f v <;> simp only [embedCode, TM2.stepAux, h, Bool.cond_false, Bool.cond_true]
      · exact ihNo v stk
      · exact ihYes v stk
  | goto f => rfl
  | halt => rfl

theorem embed_bound (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R)
    (background : Fin (l + 1) → List S) (c : Source S Q V k) (r : ℕ)
    (bound : Within r c) (room : ∀ j, (background j).length ≤ r) :
    Within r (embedConfig slots labels background c) := by
  classical
  intro j
  by_cases inside : ∃ i, slots i = j
  · obtain ⟨i, rfl⟩ := inside
    simpa [embedConfig, slots.injective.extend_apply] using bound i
  · simpa [embedConfig, Function.extend_apply' _ _ _ inside] using room j

/-- Embed a complete trace when all routine labels, including halts, agree. -/
theorem Trace.embed {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R)
    (target : R → Stmt S R V l)
    (table : ∀ q, target (labels q) = embedCode slots labels (P q))
    (background : Fin (l + 1) → List S) (room : ∀ j, (background j).length ≤ r) :
    Trace target r (embedConfig slots labels background a) (embedConfig slots labels background b) := by
  induction path with
  | refl c bound => exact .refl _ (embed_bound slots labels background c r bound room)
  | @step a c b bound next tail ih =>
      obtain ⟨q, label⟩ : ∃ q, a.l = some q := by
        cases h : a.l with
        | none => simp [step_as_map, h] at next
        | some q => exact ⟨q, rfl⟩
      have run : TM2.step target (embedConfig slots labels background a) =
          some (embedConfig slots labels background c) := by
        simp only [step_as_map, embedConfig, label, Option.map_some, table, embed_stepAux]
        have sourceStep : TM2.stepAux (P q) a.var a.stk = c := by
          simpa only [step_as_map, label, Option.map_some, Option.some.injEq] using next
        rw [sourceStep]
      exact .step (embed_bound slots labels background a r bound room) run ih

/-- The caller need only implement the routine's nonhalting labels. Its exit
label is not executed by an active-ending trace and may jump to another routine. -/
theorem Trace.embed_active {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (active : b.l ≠ none)
    (slots : Fin (k + 1) ↪ Fin (l + 1)) (labels : Q → R)
    (target : R → Stmt S R V l)
    (table : ∀ q, P q ≠ .halt → target (labels q) = embedCode slots labels (P q))
    (background : Fin (l + 1) → List S) (room : ∀ j, (background j).length ≤ r) :
    Trace target r (embedConfig slots labels background a) (embedConfig slots labels background b) := by
  induction path with
  | refl c bound => exact .refl _ (embed_bound slots labels background c r bound room)
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
      have run : TM2.step target (embedConfig slots labels background a) =
          some (embedConfig slots labels background c) := by
        simp only [step_as_map, embedConfig, label, Option.map_some, table q notHalt,
          embed_stepAux]
        have sourceStep : TM2.stepAux (P q) a.var a.stk = c := by
          simpa only [step_as_map, label, Option.map_some, Option.some.injEq] using next
        rw [sourceStep]
      exact .step (embed_bound slots labels background a r bound room) run (ih active)

/-- Renaming control labels leaves all storage and local values unchanged. -/
def renameConfig (labels : Q → R) (c : Source S Q V k) : Source S R V k :=
  ⟨c.l.map labels, c.var, c.stk⟩

theorem embed_refl (labels : Q → R) (c : Source S Q V k) :
    embedConfig (Function.Embedding.refl (Fin (k + 1))) labels (fun _ => []) c = renameConfig labels c := by
  simp only [embedConfig, renameConfig]
  congr 1
  funext j
  exact (Function.Embedding.refl (Fin (k + 1))).injective.extend_apply c.stk (fun _ => []) j

theorem Trace.rename {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (labels : Q → R) (target : R → Stmt S R V k)
    (table : ∀ q, target (labels q) = embedCode (Function.Embedding.refl _) labels (P q)) :
    Trace target r (renameConfig labels a) (renameConfig labels b) := by
  simpa only [embed_refl] using path.embed (Function.Embedding.refl _) labels target table
    (fun _ => []) (by intro j; simp)

theorem Trace.rename_active {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (active : b.l ≠ none) (labels : Q → R) (target : R → Stmt S R V k)
    (table : ∀ q, P q ≠ .halt → target (labels q) = embedCode (Function.Embedding.refl _) labels (P q)) :
    Trace target r (renameConfig labels a) (renameConfig labels b) := by
  simpa only [embed_refl] using path.embed_active active (Function.Embedding.refl _) labels target table
    (fun _ => []) (by intro j; simp)


end ComplexityOfGenerators.Simulation.StackSpace
