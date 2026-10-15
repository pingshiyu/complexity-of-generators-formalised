import ComplexityOfGenerators.Simulation.SavitchMachine.BooleanTest
import ComplexityOfGenerators.Simulation.SavitchMachine.Endpoint
import ComplexityOfGenerators.Simulation.SavitchMachine.ClearCaches
import ComplexityOfGenerators.Simulation.SavitchMachine.Alphabet

/-! Turn a destructive configuration query into a reusable Boolean test.
The endpoint column is restored by its loader, the six caches are cleared on
both outcomes, and the original input is preserved. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Query

open Turing StackSpace Frames BooleanTest
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type}

abbrev SmallMemory (α : Type) := Fin 7 → List (Alphabet α)

def small (bits : List Bool) (input : List (Alphabet α)) : SmallMemory α :=
  ![(bits.map some).map Alphabet.write, [], [], [], [], [], input]

def memory (input column : List (Alphabet α)) : Fin 8 → List (Alphabet α) :=
  ![[], [], [], [], [], [], input, column]

def slots : Fin 7 ↪ Fin 8 := ⟨Fin.castSucc, Fin.castSucc_injective 7⟩

def compile (P : Program (Alphabet α) 6) : Program (Alphabet α) 7 where
  Label := Sum Endpoint.Label (Sum P.Label ClearCaches.Label)
  finite := inferInstance
  entry := .inl .load
  exit := .inr (.inr 6)
  code
    | .inl .done => .goto fun _ => .inr (.inl P.entry)
    | .inl q => embedCode (Function.Embedding.refl _) Sum.inl
        (Endpoint.program (Alphabet.write none) (fun s => (Alphabet.read s).isSome) q)
    | .inr (.inl q) => if q = P.exit then .goto fun _ => .inr (.inr 0)
        else embedCode slots (Sum.inr ∘ Sum.inl) (P.code q)
    | .inr (.inr q) => embedCode (Function.Embedding.refl _) (Sum.inr ∘ Sum.inr) (ClearCaches.program q)
  exit_halts := rfl

theorem run (P : Program (Alphabet α) 6) (answer result : Bool)
    (bits : List Bool) (input suffix : List (Alphabet α)) (r : ℕ)
    (inputRoom : input.length ≤ r)
    (columnRoom : bits.length + 1 + suffix.length ≤ r)
    (query : ∃ stk, Trace P.code r
      (localConfig P.entry (carrying answer false) (small bits input))
      (localConfig P.exit (carrying answer result) stk) ∧ stk 6 = input) :
    Trace (compile P).code r
      (localConfig (compile P).entry (carrying answer false)
        (memory input ((bits.map some).map Alphabet.write ++ Alphabet.write none :: suffix)))
      (localConfig (compile P).exit (carrying answer result)
        (memory input ((bits.map some).map Alphabet.write ++ Alphabet.write none :: suffix))) := by
  classical
  let word := (bits.map some).map (Alphabet.write (α := α))
  let column := word ++ Alphabet.write none :: suffix
  let original := memory input column
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, memory, column, word] <;> omega
  have loaded := Endpoint.run (Alphabet.write (α := α) none) (fun s => (Alphabet.read s).isSome)
    (carrying answer false) original word suffix rfl
    (by intro s hs; simp only [word, List.mem_map] at hs; rcases hs with ⟨s, hs, rfl⟩
        rcases hs with ⟨b, hb, rfl⟩; rfl) rfl rfl rfl rfl r initial
  have first := loaded.rename_active (by simp [localConfig]) Sum.inl (compile P).code (by
    intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, localConfig, Option.map_some] at first
  let ready := Function.update original (0 : Fin 8) word
  obtain ⟨stk, queried, inputPreserved⟩ := query
  have second := queried.embed_active (by simp [localConfig]) slots (Sum.inr ∘ Sum.inl)
    (compile P).code (by
      intro q nonhalt
      have ne : q ≠ P.exit := by rintro rfl; exact nonhalt P.exit_halts
      simp only [compile, Function.comp_apply, ne, ↓reduceIte]) ready first.end_bound
  have readyLayout : Function.extend slots (small bits input) ready = ready := by
    apply extend_eq
    · intro j; fin_cases j <;> simp [slots, small, ready, original, memory, word]
    · intro j outside; rfl
  simp only [embedConfig, localConfig, Option.map_some, Function.comp_apply, readyLayout] at second
  let dirty := Function.extend slots stk ready
  have clean := (ClearCaches.run (carrying answer result) dirty r second.end_bound).rename
    (Sum.inr ∘ Sum.inr) (compile P).code (by intro q; rfl)
  simp only [renameConfig, localConfig, Option.map_some, Function.comp_apply] at clean
  have inputEq : dirty 6 = input := by
    change Function.extend slots stk ready (slots 6) = input
    rw [slots.injective.extend_apply, inputPreserved]
  have columnEq : dirty 7 = column := by
    have outside : ¬ ∃ j, slots j = (7 : Fin 8) := by
      rintro ⟨j, hj⟩; have eq := congrArg Fin.val hj
      simp only [slots, Function.Embedding.coeFn_mk, Fin.val_castSucc] at eq
      omega
    rw [show dirty 7 = Function.extend slots stk ready 7 from rfl,
      Function.extend_apply' _ _ _ outside]
    rfl
  have cleanLayout : ClearCaches.memory dirty 6 = original := by
    funext j; fin_cases j <;> simp [ClearCaches.memory, original, memory, inputEq, columnEq]
  rw [cleanLayout] at clean
  exact first.trans (.step first.end_bound rfl
    (second.trans (.step second.end_bound (by
      simp [compile, TM2.step, TM2.stepAux, localConfig, dirty]) clean)))

end
end ComplexityOfGenerators.Simulation.SavitchMachine.Query
