import ComplexityOfGenerators.Simulation.SavitchMachine.Frames
import ComplexityOfGenerators.Simulation.StackSpace.CopyTailField

/-! A finite program for constructing one field of a recursive child. The
recipe specifies a constant flag, a copy (possibly zeroed), or a decreased
depth. Every list operation is implemented by the checked stack loops. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

inductive FieldRecipe
  | flag (value : Bool)
  | copy (source : Fin 6) (zero : Bool)
  | tail (source : Fin 6)
  deriving DecidableEq, Fintype

def FieldRecipe.value (recipe : FieldRecipe) (f : Sav.Frm) : List Bool :=
  match recipe with
  | .flag b => [b]
  | .copy j zero => (field f j).map (fun b => if zero then false else b)
  | .tail j => (field f j).tail

def FieldRecipe.reads (recipe : FieldRecipe) : Option (Fin 6) :=
  match recipe with
  | .flag _ => none
  | .copy j _ | .tail j => some j

def fieldMap (zero : Bool) (s : Symbol) : Symbol := if zero then some false else s

@[simp] theorem fieldMap_bits (zero : Bool) (word : List Bool) :
    (word.map some).map (fieldMap zero) = (word.map (fun b => if zero then false else b)).map some := by
  cases zero <;> simp [fieldMap, List.map_map, Function.comp_def]

/-- The same nine finite labels suffice for any of the three field recipes. -/
def fieldCode {Q V : Type} (target : Fin 6) (recipe : FieldRecipe)
    (label : Fin 9 → Q) (exit : Q) (pc : Fin 9) : Stmt Symbol Q (V × Option Symbol) 11 :=
  match recipe with
  | .flag bit => .push (src target) (fun _ => none)
      (.push (src target) (fun _ => some bit) (.goto fun _ => exit))
  | .copy source zero => match pc.val with
      | 0 => transferCode (src source) (dst 0) (label 0) (label 1) Option.isSome
      | 1 => .push (src source) (fun _ => none) (.goto fun _ => label 2)
      | 2 => duplicateCode (dst 0) (dst 1) (src source) (label 2) (label 3)
      | 3 => transferCode (dst 1) (dst 0) (label 3) (label 7) (fun _ => true)
      | 7 => .push (src target) (fun _ => none) (.goto fun _ => label 8)
      | 8 => mapTransferCode (dst 0) (src target) (label 8) exit (fieldMap zero)
      | _ => .goto fun _ => exit
  | .tail source => match pc.val with
      | 0 => transferCode (src source) (dst 0) (label 0) (label 1) Option.isSome
      | 1 => .push (src source) (fun _ => none) (.goto fun _ => label 2)
      | 2 => duplicateCode (dst 0) (dst 1) (src source) (label 2) (label 3)
      | 3 => transferCode (dst 1) (dst 0) (label 3) (label 4) (fun _ => true)
      | 4 => transferCode (dst 0) (dst 1) (label 4) (label 5) (fun _ => true)
      | 5 => .pop (dst 1) (fun v _ => v) (.goto fun _ => label 6)
      | 6 => transferCode (dst 1) (dst 0) (label 6) (label 7) (fun _ => true)
      | 7 => .push (src target) (fun _ => none) (.goto fun _ => label 8)
      | _ => mapTransferCode (dst 0) (src target) (label 8) exit id

/-- Correctness of a field recipe in an arbitrary larger program. All
suspended data are preserved, and both scratch registers end empty. -/
theorem field_trace {Q V : Type} (P : Q → Stmt Symbol Q (V × Option Symbol) 11)
    (target : Fin 6) (recipe : FieldRecipe) (label : Fin 9 → Q) (exit : Q)
    (table : ∀ pc, P (label pc) = fieldCode target recipe label exit pc)
    (v : V) (stk : Memory) (f : Sav.Frm)
    (readable : ∀ j, recipe.reads = some j → ∃ suffix,
      stk (src j) = (field f j).map some ++ none :: suffix)
    (empty₀ : stk (dst 0) = []) (empty₁ : stk (dst 1) = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : (recipe.value f).length + 1 + (stk (src target)).length ≤ r) :
    Trace P r (localConfig (label 0) v stk)
      (localConfig exit v (Function.update stk (src target)
        ((recipe.value f).map some ++ none :: stk (src target)))) := by
  cases recipe with
  | flag bit =>
      have next : TM2.step P (localConfig (label 0) v stk) =
          some (localConfig exit v (Function.update stk (src target)
            (some bit :: none :: stk (src target)))) := by
        simp [TM2.step, localConfig, table, fieldCode, TM2.stepAux, Function.update_idem]
      apply Trace.step (show Within r (localConfig (label 0) v stk) from bound) next
      apply Trace.refl
      intro j
      by_cases h : j = src target
      · subst j
        simp only [FieldRecipe.value, List.length_cons, List.length_nil] at room
        simp only [localConfig, Function.update_self, List.length_cons]
        omega
      · simpa [localConfig, Function.update_of_ne h] using bound j
  | copy source zero =>
      obtain ⟨suffix, head⟩ := readable source rfl
      have path := copy_field P (src source) (src target) (dst 0) (dst 1)
        (src_ne_dst _ _) (src_ne_dst _ _) (by decide) (src_ne_dst _ _)
        (label 0) (label 1) (label 2) (label 3) (label 7) (label 8) exit none Option.isSome (fieldMap zero)
        (table 0) (table 1) (table 2) (table 3) (table 7) (table 8)
        v stk ((field f source).map some) suffix head (by intro s hs; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs; rfl) rfl empty₀ empty₁ r bound (by
          simpa only [List.length_map, FieldRecipe.value] using room)
      simpa only [FieldRecipe.value, fieldMap_bits] using path
  | tail source =>
      obtain ⟨suffix, head⟩ := readable source rfl
      have path := copy_tail_field P (src source) (src target) (dst 0) (dst 1)
        (src_ne_dst _ _) (src_ne_dst _ _) (by decide) (src_ne_dst _ _)
        (label 0) (label 1) (label 2) (label 3) (label 4) (label 5) (label 6) (label 7) (label 8) exit
        none Option.isSome (table 0) (table 1) (table 2) (table 3) (table 4) (table 5) (table 6) (table 7) (table 8)
        v stk ((field f source).map some) suffix head (by intro s hs; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs; rfl) rfl empty₀ empty₁ r bound (by
          simpa only [← List.map_tail, List.length_map, FieldRecipe.value] using room)
      simpa only [FieldRecipe.value, ← List.map_tail] using path

/-- Child construction uses only the parent's current fields. Zeroing a
copy of its midpoint preserves the fixed configuration-code width. -/
def childRecipe (kind phase : Bool) : Fin 6 → FieldRecipe :=
  ![.flag (phase && kind), .flag false, .tail 2,
    .copy (if phase then 5 else 3) false,
    (if phase then if kind then .copy 5 true else .copy 4 false else .copy 5 false),
    .copy 5 true]

theorem childRecipe_value (f : Sav.Frm) (j : Fin 6) :
    (childRecipe f.kind f.ph j).value f =
      field (Sav.child (List.replicate f.m.length false) f) j := by
  cases kind : f.kind <;> cases phase : f.ph <;> fin_cases j <;>
    simp [childRecipe, FieldRecipe.value, Sav.child, field, kind, phase, List.drop_one]

theorem childRecipe_source (kind phase : Bool) (j source : Fin 6)
    (reads : (childRecipe kind phase j).reads = some source) : j.val ≤ source.val := by
  cases kind <;> cases phase <;> fin_cases j <;>
    simp [childRecipe, FieldRecipe.reads] at reads <;> subst source <;> decide

end ComplexityOfGenerators.Simulation.SavitchMachine
