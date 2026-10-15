import ComplexityOfGenerators.Simulation.SavitchMachine.Query

/-! A cache-restoring two-endpoint query. The two columns and the persistent
input occupy independent stacks, so source and target queries can be composed
without changing suspended Savitch frames. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.PairQuery

open Turing StackSpace Frames BooleanTest
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type}

def memory (input source target : List (Alphabet α)) : Fin 9 → List (Alphabet α) :=
  ![[], [], [], [], [], [], input, source, target]

def slots : Fin 8 ↪ Fin 9 := ⟨![0, 1, 2, 3, 4, 5, 6, 8], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def compile (P : Program (Alphabet α) 7) : Program (Alphabet α) 8 where
  Label := Sum Endpoint.Label (Sum P.Label ClearCaches.Label)
  finite := inferInstance
  entry := .inl .load
  exit := .inr (.inr 6)
  code
    | .inl .done => .goto fun _ => .inr (.inl P.entry)
    | .inl q => embedCode (Function.Embedding.refl _) Sum.inl
        (extendCode (Endpoint.program (Alphabet.write none) (fun s => (Alphabet.read s).isSome) q))
    | .inr (.inl q) => if q = P.exit then .goto fun _ => .inr (.inr 0)
        else embedCode slots (Sum.inr ∘ Sum.inl) (P.code q)
    | .inr (.inr q) => embedCode (Function.Embedding.refl _) (Sum.inr ∘ Sum.inr)
        (extendCode (ClearCaches.program q))
  exit_halts := rfl

theorem run (P : Program (Alphabet α) 7) (answer result : Bool)
    (bits : List Bool) (input parents target : List (Alphabet α)) (r : ℕ)
    (inputRoom : input.length ≤ r) (sourceRoom : bits.length + 1 + parents.length ≤ r)
    (targetRoom : target.length ≤ r)
    (query : ∃ stk, Trace P.code r
      (localConfig P.entry (carrying answer false) (Fin.snoc (Query.small bits input) target))
      (localConfig P.exit (carrying answer result) stk) ∧ stk 6 = input ∧ stk 7 = target) :
    let source := (bits.map some).map Alphabet.write ++ Alphabet.write none :: parents
    Trace (compile P).code r
      (localConfig (compile P).entry (carrying answer false) (memory input source target))
      (localConfig (compile P).exit (carrying answer result) (memory input source target)) := by
  let word := (bits.map some).map (Alphabet.write (α := α))
  let source := word ++ Alphabet.write none :: parents
  let original := memory input source target
  let front := Query.memory input source
  have bound : ∀ j, (front j).length ≤ r := by
    intro j; fin_cases j <;> simp [front, Query.memory, source, word] <;> omega
  have loaded := Endpoint.run (Alphabet.write (α := α) none) (fun s => (Alphabet.read s).isSome)
    (carrying answer false) front word parents rfl
    (by intro s hs; simp only [word, List.mem_map] at hs; rcases hs with ⟨s, hs, rfl⟩
        rcases hs with ⟨b, hb, rfl⟩; rfl) rfl rfl rfl rfl r bound
  have first := (loaded.extend target targetRoom).rename_active
    (by simp [extendConfig, localConfig]) Sum.inl (compile P).code (by
      intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, extendConfig, localConfig, Option.map_some] at first
  let ready := Function.update original (0 : Fin 9) word
  have firstLayout : Fin.snoc front target = original := by
    funext j; fin_cases j <;> simp [front, Query.memory, original, memory, Fin.snoc] <;> rfl
  have readyLayout : Fin.snoc (Function.update front (0 : Fin 8) word) target = ready := by
    funext j; fin_cases j <;> simp [front, Query.memory, original, memory, ready, Fin.snoc] <;> rfl
  rw [firstLayout, readyLayout] at first
  obtain ⟨stk, queried, inputPreserved, targetPreserved⟩ := query
  have second := queried.embed_active (by simp [localConfig]) slots (Sum.inr ∘ Sum.inl)
    (compile P).code (by
      intro q nonhalt
      have ne : q ≠ P.exit := by rintro rfl; exact nonhalt P.exit_halts
      simp only [compile, Function.comp_apply, ne, ↓reduceIte]) ready first.end_bound
  have queryLayout : Function.extend slots (Fin.snoc (Query.small bits input) target) ready = ready := by
    apply extend_eq
    · intro j; fin_cases j <;> simp [slots, Query.small, ready, original, memory, word, Fin.snoc] <;> rfl
    · intro j outside; rfl
  simp only [embedConfig, localConfig, Option.map_some, Function.comp_apply, queryLayout] at second
  let dirty := Function.extend slots stk ready
  have inputEq : dirty 6 = input := by
    change Function.extend slots stk ready (slots 6) = input
    rw [slots.injective.extend_apply, inputPreserved]
  have targetEq : dirty 8 = target := by
    change Function.extend slots stk ready (slots 7) = target
    rw [slots.injective.extend_apply, targetPreserved]
  have sourceEq : dirty 7 = source := by
    have outside : ¬ ∃ j, slots j = (7 : Fin 9) := by simp [slots, Fin.exists_fin_succ]
    rw [show dirty 7 = Function.extend slots stk ready 7 from rfl, Function.extend_apply' _ _ _ outside]
    rfl
  let dirtyPrefix : Fin 8 → List (Alphabet α) := fun j => dirty j.castSucc
  have prefixBound : ∀ j, (dirtyPrefix j).length ≤ r := fun j => second.end_bound j.castSucc
  have cleaned := ((ClearCaches.run (carrying answer result) dirtyPrefix r prefixBound).extend
    (dirty 8) (second.end_bound 8)).rename (Sum.inr ∘ Sum.inr) (compile P).code (fun _ => rfl)
  simp only [renameConfig, extendConfig, localConfig, Option.map_some, Function.comp_apply] at cleaned
  have dirtyLayout : Fin.snoc dirtyPrefix (dirty 8) = dirty := by
    funext j; fin_cases j <;> simp [dirtyPrefix, Fin.snoc] <;> rfl
  have cleanLayout : Fin.snoc (ClearCaches.memory dirtyPrefix 6) (dirty 8) = original := by
    funext j; fin_cases j <;> simp [ClearCaches.memory, dirtyPrefix, original, memory,
      inputEq, sourceEq, targetEq, Fin.snoc] <;> rfl
  rw [dirtyLayout, cleanLayout] at cleaned
  exact first.trans (.step first.end_bound rfl (second.trans (.step second.end_bound
    (by simp [compile, TM2.step, TM2.stepAux, localConfig, dirty]) cleaned)))

end
end ComplexityOfGenerators.Simulation.SavitchMachine.PairQuery
