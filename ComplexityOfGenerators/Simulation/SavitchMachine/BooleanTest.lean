import ComplexityOfGenerators.Simulation.SavitchMachine.FieldCounter
import ComplexityOfGenerators.Simulation.StackSpace.Embed

/-! Composition of finite, space-bounded tests. Each test restores its stacks,
so conjunction and disjunction need no additional registers. The finite control
contains only the component program counters, never an input-dependent value. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.BooleanTest

open Turing StackSpace
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

variable (S : Type) (k : ℕ)

structure Program where
  Label : Type
  finite : Fintype Label
  entry : Label
  exit : Label
  code : Label → Stmt S Label (Status × Option S) k
  exit_halts : code exit = .halt

attribute [instance] Program.finite

variable {S k} {X : Type}

def Correct (P : Program S k) (radius : X → ℕ)
    (memory : X → Fin (k + 1) → List S) (value : X → Bool) : Prop :=
  ∀ x answer, Trace P.code (radius x)
    (localConfig P.entry (carrying answer false) (memory x))
    (localConfig P.exit (carrying answer (value x)) (memory x))

def Realizable (radius : X → ℕ) (memory : X → Fin (k + 1) → List S)
    (value : X → Bool) : Prop := ∃ P : Program S k, Correct P radius memory value

/-- Specialize an already verified test to another family of inputs. -/
theorem Realizable.comap {Y : Type} {radius : X → ℕ}
    {memory : X → Fin (k + 1) → List S} {value : X → Bool}
    (h : Realizable radius memory value) (f : Y → X) :
    Realizable (radius ∘ f) (memory ∘ f) (value ∘ f) := by
  obtain ⟨P, correct⟩ := h
  exact ⟨P, fun x answer => correct (f x) answer⟩

/-- Stop on `short`; otherwise run the second test. -/
def join (short : Bool) (P Q : Program S k) : Program S k where
  Label := Option (Sum P.Label Q.Label)
  finite := inferInstance
  entry := some (.inl P.entry)
  exit := none
  code
    | none => .halt
    | some (.inl p) => if p = P.exit then
        .branch (fun v => v.1.returned.getD false == short)
          (.goto fun _ => none)
          (.load (fun v => (carrying v.1.answer false, none))
            (.goto fun _ => some (.inr Q.entry)))
        else embedCode (Function.Embedding.refl _) (some ∘ Sum.inl) (P.code p)
    | some (.inr q) => if q = Q.exit then .goto fun _ => none
        else embedCode (Function.Embedding.refl _) (some ∘ Sum.inr) (Q.code q)
  exit_halts := rfl

theorem join_correct (short : Bool) {P Q : Program S k}
    {radius : X → ℕ} {memory : X → Fin (k + 1) → List S} {p q : X → Bool}
    (hp : Correct P radius memory p) (hq : Correct Q radius memory q) :
    Correct (join short P Q) radius memory (fun x => if p x = short then short else q x) := by
  classical
  intro x answer
  have first := (hp x answer).rename_active (by simp [localConfig])
    (some ∘ Sum.inl) (join short P Q).code (by
      intro pc active
      have ne : pc ≠ P.exit := by rintro rfl; exact active P.exit_halts
      simp only [join, Function.comp_apply, ne, ↓reduceIte])
  have last := (hq x answer).rename_active (by simp [localConfig])
    (some ∘ Sum.inr) (join short P Q).code (by
      intro pc active
      have ne : pc ≠ Q.exit := by rintro rfl; exact active Q.exit_halts
      simp only [join, Function.comp_apply, ne, ↓reduceIte])
  simp only [renameConfig, localConfig, Option.map_some, Function.comp_apply] at first last
  by_cases stop : p x = short
  · simp only [stop, ↓reduceIte] at first ⊢
    exact first.trans (.step first.end_bound (by
      simp [join, TM2.step, TM2.stepAux, localConfig, carrying]) (.refl _ first.end_bound))
  · simp only [stop, ↓reduceIte]
    exact first.trans (.step first.end_bound (by
      simp [join, TM2.step, TM2.stepAux, localConfig, carrying, stop])
      (last.trans (.step last.end_bound (by simp [join, TM2.step, TM2.stepAux, localConfig])
        (.refl _ last.end_bound))))

def constant (value : Bool) : Program S k where
  Label := Bool
  finite := inferInstance
  entry := false
  exit := true
  code
    | false => .load (fun v => (carrying v.1.answer value, none)) (.goto fun _ => true)
    | true => .halt
  exit_halts := rfl

theorem constant_correct (value : Bool) (radius : X → ℕ)
    (memory : X → Fin (k + 1) → List S) (bound : ∀ x j, (memory x j).length ≤ radius x) :
    Correct (constant value) radius memory (fun _ => value) := by
  intro x answer
  exact .step (bound x) rfl (.refl _ (bound x))

theorem Realizable.and {radius : X → ℕ} {memory : X → Fin (k + 1) → List S}
    {p q : X → Bool} (hp : Realizable radius memory p) (hq : Realizable radius memory q) :
    Realizable radius memory (fun x => p x && q x) := by
  obtain ⟨P, hp⟩ := hp
  obtain ⟨Q, hq⟩ := hq
  refine ⟨join false P Q, ?_⟩
  have h := join_correct false hp hq
  have eq : (fun x => if p x = false then false else q x) = (fun x => p x && q x) := by
    funext x; cases p x <;> rfl
  rwa [eq] at h

theorem Realizable.or {radius : X → ℕ} {memory : X → Fin (k + 1) → List S}
    {p q : X → Bool} (hp : Realizable radius memory p) (hq : Realizable radius memory q) :
    Realizable radius memory (fun x => p x || q x) := by
  obtain ⟨P, hp⟩ := hp
  obtain ⟨Q, hq⟩ := hq
  refine ⟨join true P Q, ?_⟩
  have h := join_correct true hp hq
  have eq : (fun x => if p x = true then true else q x) = (fun x => p x || q x) := by
    funext x; cases p x <;> rfl
  rwa [eq] at h

theorem Realizable.any {C : Type} {radius : X → ℕ}
    {memory : X → Fin (k + 1) → List S} (bound : ∀ x j, (memory x j).length ≤ radius x)
    (candidates : List C) (test : C → X → Bool)
    (each : ∀ c ∈ candidates, Realizable radius memory (test c)) :
    Realizable radius memory (fun x => candidates.any (fun c => test c x)) := by
  induction candidates with
  | nil => exact ⟨constant false, constant_correct false radius memory bound⟩
  | cons c cs ih =>
      exact (each c (by simp)).or (ih (fun a ha => each a (by simp [ha])))

/-- Sequential composition also supports destructive preparation routines.
The first routine's result and stacks pass unchanged to the second. -/
def chain (P Q : Program S k) : Program S k where
  Label := Sum P.Label Q.Label
  finite := inferInstance
  entry := .inl P.entry
  exit := .inr Q.exit
  code
    | .inl p => if p = P.exit then .goto fun _ => .inr Q.entry
        else embedCode (Function.Embedding.refl _) Sum.inl (P.code p)
    | .inr q => embedCode (Function.Embedding.refl _) Sum.inr (Q.code q)
  exit_halts := by simp only [Q.exit_halts, embedCode]

theorem chain_trace (P Q : Program S k) (r : ℕ) (v w z : Status)
    (a b c : Fin (k + 1) → List S)
    (first : Trace P.code r (localConfig P.entry v a) (localConfig P.exit w b))
    (last : Trace Q.code r (localConfig Q.entry w b) (localConfig Q.exit z c)) :
    Trace (chain P Q).code r
      (localConfig (chain P Q).entry v a) (localConfig (chain P Q).exit z c) := by
  have initial := first.rename_active (by simp [localConfig]) Sum.inl (chain P Q).code (by
    intro pc nonhalt
    have ne : pc ≠ P.exit := by rintro rfl; exact nonhalt P.exit_halts
    simp only [chain, ne, ↓reduceIte])
  have final := last.rename Sum.inr (chain P Q).code (fun _ => rfl)
  simp only [renameConfig, localConfig, Option.map_some] at initial final
  exact initial.trans (.step initial.end_bound (by simp [chain, TM2.step, TM2.stepAux, localConfig]) final)

/-- Add one untouched persistent stack to a finite program. -/
def extend (P : Program S k) : Program S (k + 1) where
  Label := P.Label
  finite := P.finite
  entry := P.entry
  exit := P.exit
  code q := extendCode (P.code q)
  exit_halts := by simp only [P.exit_halts, extendCode]

/-- A test can select registers of a larger machine without changing the
unselected stacks. This lets endpoint tests share the recursive frame store. -/
def embed {l : ℕ} (slots : Fin (k + 1) ↪ Fin (l + 1)) (P : Program S k) : Program S l where
  Label := P.Label
  finite := P.finite
  entry := P.entry
  exit := P.exit
  code q := embedCode slots id (P.code q)
  exit_halts := by simp only [P.exit_halts, embedCode]

theorem Realizable.embed {l : ℕ} {radius : X → ℕ}
    {memory : X → Fin (k + 1) → List S} {value : X → Bool}
    (h : Realizable radius memory value) (slots : Fin (k + 1) ↪ Fin (l + 1))
    (target : X → Fin (l + 1) → List S)
    (selected : ∀ x j, target x (slots j) = memory x j)
    (bound : ∀ x j, (target x j).length ≤ radius x) :
    Realizable radius target value := by
  obtain ⟨P, correct⟩ := h
  refine ⟨BooleanTest.embed slots P, ?_⟩
  intro x answer
  have traced := (correct x answer).embed slots id (BooleanTest.embed slots P).code
    (by intro q; rfl) (target x) (bound x)
  have layout : Function.extend slots (memory x) (target x) = target x :=
    extend_eq slots (target x) (target x) (memory x) (selected x) (fun _ _ => rfl)
  simpa only [embedConfig, localConfig, Option.map_some, id_eq, layout, BooleanTest.embed] using traced

/-- A finite disjunction is compiled by enumerating machine-dependent
candidates in finite control. No candidate list is stored on the work tape. -/
theorem Realizable.exists {C : Type} [Fintype C] {radius : X → ℕ}
    {memory : X → Fin (k + 1) → List S} (bound : ∀ x j, (memory x j).length ≤ radius x)
    (test : C → X → Bool) (each : ∀ c, Realizable radius memory (test c)) :
    Realizable radius memory (fun x => decide (∃ c, test c x = true)) := by
  classical
  have h := Realizable.any bound (Finset.univ.toList : List C) test (fun c _ => each c)
  have eq : (fun x => (Finset.univ.toList : List C).any (fun c => test c x)) =
      (fun x => decide (∃ c, test c x = true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  rwa [eq] at h

end
end ComplexityOfGenerators.Simulation.SavitchMachine.BooleanTest
