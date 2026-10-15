import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateEncode
import ComplexityOfGenerators.Simulation.StackSpace.Embed
import ComplexityOfGenerators.Simulation.StackSpace.Expand
import ComplexityOfGenerators.Foundations.InitialSpaceCode

/-! Build the native initial-configuration bit string from the space ruler
and the input-length-plus-one ruler. All variable-size fields are written by
finite loops; only the machine's initial control code is a program literal. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.InitialVertex

open Turing StackSpace Frames Complexity
open CoordinateEncode (unary)
set_option backward.isDefEq.respectTransparency false

inductive Label
  | seed | inputZeros | extraInput | copySpace | duplicateSpace | doubleSpace | extraSpace
  | coordinate (pc : CoordinateEncode.Label)
  | head | blank | done
  deriving DecidableEq, Fintype

def slots : Fin 4 ↪ Fin 6 := ⟨Fin.castAdd 2, fun _ _ h => (Fin.castAdd_inj (n := 2)).mp h⟩

private theorem extend_slots (front : Fin 4 → List Symbol) (background : Fin 6 → List Symbol) :
    Function.extend slots front background = ![front 0, front 1, front 2, front 3, background 4, background 5] := by
  funext j
  fin_cases j
  · exact slots.injective.extend_apply front background 0
  · exact slots.injective.extend_apply front background 1
  · exact slots.injective.extend_apply front background 2
  · exact slots.injective.extend_apply front background 3
  · exact Function.extend_apply' front background 4 (by simp [slots, Fin.exists_fin_succ])
  · exact Function.extend_apply' front background 5 (by simp [slots, Fin.exists_fin_succ])

def program (state : List Bool) (symbols : ℕ) : Label → Stmt Symbol Label Local 5
  | .seed => pushLiteral 5 (state.map some) (.goto fun _ => .inputZeros)
  | .inputZeros => expandCode 1 5 (some false) 2 .inputZeros .extraInput
  | .extraInput => .push 5 (fun _ => some false) (.goto fun _ => .copySpace)
  | .copySpace => transferCode 0 2 .copySpace .duplicateSpace (fun _ => true)
  | .duplicateSpace => duplicateCode 2 0 4 .duplicateSpace .doubleSpace
  | .doubleSpace => expandCode 4 1 (some false) 2 .doubleSpace .extraSpace
  | .extraSpace => .push 1 (fun _ => some false) (.goto fun _ => .coordinate .seed)
  | .coordinate .done => .goto fun _ => .head
  | .coordinate pc => embedCode slots Label.coordinate (CoordinateEncode.program pc)
  | .head => transferCode 2 5 .head .blank Option.isSome
  | .blank => expandCode 1 5 (some false) (symbols + 1) .blank .done
  | .done => .halt

def code (state : List Bool) (symbols n s : ℕ) : List Bool :=
  state ++ List.replicate (2 * n + 3) false ++ bitsOfLenLE (2 * s + 1) s ++
    List.replicate ((symbols + 1) * (2 * s + 1)) false

theorem code_length (state : List Bool) (symbols n s : ℕ) :
    (code state symbols n s).length = state.length + (2 * n + 3) + (2 * s + 1) +
      (symbols + 1) * (2 * s + 1) := by simp [code, Nat.add_assoc]

def radius (state : List Bool) (symbols n s : ℕ) : ℕ :=
  state.length + 2 * n + 6 * s + (symbols + 1) * (2 * s + 1) + 10

/-- The initializer produces the reversed code, which is precisely the
representation expected in the root frame's cache register. It consumes both
rulers and clears all temporary registers. -/
theorem build (state : List Bool) (symbols n s : ℕ) :
    Trace (program state symbols) (radius state symbols n s)
      (localConfig .seed (carrying false false) ![unary s, unary (n + 1), [], [], [], []])
      (localConfig .done (carrying false false) ![[], [], [], [], [], (code state symbols n s).reverse.map some]) := by
  let P := program state symbols
  let r := radius state symbols n s
  let v := carrying false false
  let original : Fin 6 → List Symbol := ![unary s, unary (n + 1), [], [], [], []]
  let seeded : Fin 6 → List Symbol := ![unary s, unary (n + 1), [], [], [], state.reverse.map some]
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, r, radius] <;> omega
  have seedBound : ∀ j, (seeded j).length ≤ r := by
    intro j; fin_cases j <;> simp [seeded, r, radius] <;> omega
  have seed : TM2.step P (localConfig .seed v original) = some (localConfig .inputZeros v seeded) := by
    simp [P, program, TM2.step, localConfig, pushLiteral_stepAux, TM2.stepAux, original, seeded,
      ← List.map_reverse]
    funext j; fin_cases j <;> simp [Function.update_apply]
  have inputZeros := expand_all P 1 5 (by decide) (some false) 2 .inputZeros .extraInput rfl
    v seeded r seedBound (by simp [seeded, r, radius]; omega)
  let copiedInput : Fin 6 → List Symbol :=
    ![unary s, [], [], [], [], unary (2 * (n + 1)) ++ state.reverse.map some]
  have inputMemory : replaceTwo seeded (1 : Fin 6) 5 []
      (unary (2 * (seeded 1).length) ++ seeded 5) = copiedInput := by
    funext j; fin_cases j <;> simp [seeded, copiedInput, replaceTwo, Function.update_apply]
  rw [inputMemory] at inputZeros
  let front := state ++ List.replicate (2 * n + 3) false
  let inputReady : Fin 6 → List Symbol := ![unary s, [], [], [], [], front.reverse.map some]
  have extraInput : TM2.step P (localConfig .extraInput v copiedInput) =
      some (localConfig .copySpace v inputReady) := by
    simp [P, program, TM2.step, localConfig, TM2.stepAux, copiedInput, inputReady]
    funext j
    fin_cases j <;> simp [Function.update_apply, front, List.replicate_succ, show 2 * n + 3 = 2 * (n + 1) + 1 by omega]
    rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
    simp only [List.append_assoc, List.singleton_append]
  have inputBound : ∀ j, (inputReady j).length ≤ r := by
    intro j; fin_cases j <;> simp [inputReady, front, r, radius] <;> omega
  have copiedSpace := copy_all P 2 0 4 .duplicateSpace .doubleSpace .copySpace rfl rfl
    (by decide) (by decide) (by decide) v inputReady rfl r inputBound (by simp [inputReady, r, radius] <;> omega)
  let spaceCopied : Fin 6 → List Symbol := ![unary s, [], [], [], unary s, front.reverse.map some]
  have spaceMemory : Function.update inputReady (4 : Fin 6) (inputReady 0 ++ inputReady 4) = spaceCopied := by
    funext j; fin_cases j <;> simp [inputReady, spaceCopied, Function.update_apply]
  rw [spaceMemory] at copiedSpace
  have doubled := expand_all P 4 1 (by decide) (some false) 2 .doubleSpace .extraSpace rfl
    v spaceCopied r copiedSpace.end_bound (by simp [spaceCopied, r, radius] <;> omega)
  let spaceDoubled : Fin 6 → List Symbol := ![unary s, unary (2 * s), [], [], [], front.reverse.map some]
  have doubledMemory : replaceTwo spaceCopied (4 : Fin 6) 1 []
      (unary (2 * (spaceCopied 4).length) ++ spaceCopied 1) = spaceDoubled := by
    funext j; fin_cases j <;> simp [spaceCopied, spaceDoubled, replaceTwo, Function.update_apply]
  rw [doubledMemory] at doubled
  let ready : Fin 6 → List Symbol := ![unary s, unary (2 * s + 1), [], [], [], front.reverse.map some]
  have extraSpace : TM2.step P (localConfig .extraSpace v spaceDoubled) =
      some (localConfig (.coordinate .seed) v ready) := by
    simp [P, program, TM2.step, localConfig, TM2.stepAux, spaceDoubled, ready]
    funext j; fin_cases j <;> simp [Function.update_apply, List.replicate_succ]
  have readyBound : ∀ j, (ready j).length ≤ r := by
    intro j; fin_cases j <;> simp [ready, front, r, radius] <;> omega
  have encoded := ((CoordinateEncode.encode false s (2 * s + 1)
    ((show s < 2 * s + 1 by omega).trans Nat.lt_two_pow_self)).mono
      (show s + (2 * s + 1) + 1 ≤ r by dsimp [r, radius]; omega)).embed_active
    (by simp [localConfig]) slots Label.coordinate P
    (by intro pc nonhalt; cases pc <;> first | rfl | exact False.elim (nonhalt rfl)) ready readyBound
  have before : embedConfig slots Label.coordinate ready
      (localConfig CoordinateEncode.Label.seed (carrying false false)
        ![unary s, unary (2 * s + 1), [], []]) = localConfig (.coordinate .seed) v ready := by
    simp only [embedConfig, localConfig, Option.map_some]
    congr 1
    exact extend_slots _ ready
  let headBits := bitsOfLenLE (2 * s + 1) s
  let withHead : Fin 6 → List Symbol := ![[], unary (2 * s + 1), headBits.map some ++ [none], [], [], front.reverse.map some]
  have after : embedConfig slots Label.coordinate ready
      (localConfig CoordinateEncode.Label.done (carrying false false)
        (CoordinateEncode.registers 0 (2 * s + 1) headBits)) =
      localConfig (.coordinate .done) v withHead := by
    simp only [embedConfig, localConfig, Option.map_some]
    congr 1
    exact extend_slots _ ready
  rw [before, after] at encoded
  have resume : TM2.step P (localConfig (.coordinate .done) v withHead) =
      some (localConfig .head v withHead) := rfl
  have head := transfer_field P 2 5 (by decide) .head .blank Option.isSome rfl v withHead
    (headBits.map some) none [] rfl (by intro a h; simp only [List.mem_map] at h; obtain ⟨b, _, rfl⟩ := h; rfl)
    rfl r encoded.end_bound (by simp [withHead, headBits, front, r, radius] <;> omega)
  let prefixCode := front ++ headBits
  let prefixReady : Fin 6 → List Symbol := ![[], unary (2 * s + 1), [], [], [], prefixCode.reverse.map some]
  have headMemory : replaceTwo withHead (2 : Fin 6) 5 []
      ((headBits.map some).reverse ++ withHead 5) = prefixReady := by
    funext j
    fin_cases j <;> simp [withHead, prefixReady, prefixCode, replaceTwo, Function.update_apply, ← List.map_reverse]
  rw [headMemory] at head
  have blank := expand_all P 1 5 (by decide) (some false) (symbols + 1) .blank .done rfl
    v prefixReady r head.end_bound (by simp [prefixReady, prefixCode, headBits, front, r, radius]; omega)
  have finalMemory : replaceTwo prefixReady (1 : Fin 6) 5 []
      (unary ((symbols + 1) * (prefixReady 1).length) ++ prefixReady 5) =
      ![[], [], [], [], [], (code state symbols n s).reverse.map some] := by
    funext j
    fin_cases j <;> simp [prefixReady, prefixCode, front, headBits, code, replaceTwo, Function.update_apply,
      ← List.map_reverse, List.append_assoc]
  rw [finalMemory] at blank
  exact .step initial seed (inputZeros.trans (.step inputZeros.end_bound extraInput
    (copiedSpace.trans (doubled.trans (.step doubled.end_bound extraSpace
      (encoded.trans (.step encoded.end_bound resume (head.trans blank))))))))

end ComplexityOfGenerators.Simulation.SavitchMachine.InitialVertex
