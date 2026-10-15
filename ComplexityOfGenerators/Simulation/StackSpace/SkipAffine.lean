import ComplexityOfGenerators.Simulation.StackSpace.Copy
import ComplexityOfGenerators.Simulation.StackSpace.MapTransfer
import ComplexityOfGenerators.Simulation.StackSpace.Expand
import ComplexityOfGenerators.Simulation.StackSpace.ReadAt

/-! Skip a configuration-header prefix of length `a * input.length + b`.
All header offsets have this form. The coefficients belong to the finite
program, while the input length is obtained by a symbol-by-symbol scan. -/

namespace ComplexityOfGenerators.Simulation.StackSpace.SkipAffine

open Turing
set_option backward.isDefEq.respectTransparency false
variable {S V : Type} [Inhabited S]

inductive Label | copy | duplicate | map | scale | offset | drop | inspect | done
  deriving DecidableEq, Fintype

def program (symbol : S) (a b : ℕ) : Label → Stmt S Label (V × Option S) 3
  | .copy => transferCode 1 3 .copy .duplicate (fun _ => true)
  | .duplicate => duplicateCode 3 1 2 .duplicate .map
  | .map => mapTransferCode 2 3 .map .scale (fun _ => symbol)
  | .scale => expandCode 3 2 symbol a .scale .offset
  | .offset => pushCopies 2 symbol b (.goto fun _ => .drop)
  | .drop => readAtCode 0 2 .drop .inspect
  | .inspect => inspectCode 0 (fun _ v => v) .done
  | .done => .halt

def registers (source input : List S) : Fin 4 → List S := ![source, input, [], []]

/-- The affine prefix is discarded without changing the persistent input or
leaking scratch storage. This also handles truncated configuration strings. -/
theorem run (symbol : S) (a b : ℕ) (v : V) (source input : List S) (r : ℕ)
    (sourceRoom : source.length ≤ r) (inputRoom : input.length ≤ r)
    (counterRoom : a * input.length + b ≤ r) :
    Trace (program symbol a b) r (localConfig .copy v (registers source input))
      (localConfig .done v (registers (source.drop (a * input.length + b)) input)) := by
  let P := program (V := V) symbol a b
  have initial : ∀ j, (registers source input j).length ≤ r := by
    intro j; fin_cases j <;> simp [registers] <;> assumption
  have copied := copy_all P 3 1 2 .duplicate .map .copy rfl rfl (by decide) (by decide) (by decide)
    v (registers source input) rfl r initial (by simpa [registers] using inputRoom)
  let withCopy : Fin 4 → List S := ![source, input, input, []]
  have copiedMemory : Function.update (registers source input) (2 : Fin 4)
      (registers source input 1 ++ registers source input 2) = withCopy := by
    funext j; fin_cases j <;> simp [registers, withCopy]
  rw [copiedMemory] at copied
  have mapped := mapTransfer_all P 2 3 (by decide) .map .scale (fun _ => symbol) rfl v withCopy r
    copied.end_bound (by simpa [withCopy] using inputRoom)
  let measured : Fin 4 → List S := ![source, input, [], List.replicate input.length symbol]
  have mappedMemory : replaceTwo withCopy (2 : Fin 4) 3 []
      ((withCopy 2).reverse.map (fun _ => symbol) ++ withCopy 3) = measured := by
    funext j; fin_cases j <;> simp [withCopy, measured, replaceTwo, List.map_const']
  rw [mappedMemory] at mapped
  have scaled := expand_all P 3 2 (by decide) symbol a .scale .offset rfl v measured r
    mapped.end_bound (by simp [measured]; omega)
  let scaledMemory : Fin 4 → List S := ![source, input, List.replicate (a * input.length) symbol, []]
  have scaleLayout : replaceTwo measured (3 : Fin 4) 2 []
      (List.replicate (a * (measured 3).length) symbol ++ measured 2) = scaledMemory := by
    funext j; fin_cases j <;> simp [measured, scaledMemory, replaceTwo]
  rw [scaleLayout] at scaled
  let ready : Fin 4 → List S := ![source, input, List.replicate (a * input.length + b) symbol, []]
  have offset : TM2.step P (localConfig .offset v scaledMemory) = some (localConfig .drop v ready) := by
    simp only [P, TM2.step, localConfig, program, pushCopies_stepAux, TM2.stepAux]
    congr 2
    funext j
    fin_cases j <;> simp [scaledMemory, ready, ← List.replicate_add, Nat.add_comm]
  have readyBound : ∀ j, (ready j).length ≤ r := by
    intro j; fin_cases j <;> simp [ready] <;> assumption
  have skipped := readAt_trace P 0 2 (by decide) .drop .inspect rfl .done (fun _ v => v) rfl
    v ready r readyBound
  have finalMemory : replaceTwo ready (0 : Fin 4) 2 ((ready 0).drop (ready 2).length) [] =
      registers (source.drop (a * input.length + b)) input := by
    funext j; fin_cases j <;> simp [ready, registers, replaceTwo]
  rw [finalMemory] at skipped
  exact copied.trans (mapped.trans (scaled.trans (.step scaled.end_bound offset skipped)))

end ComplexityOfGenerators.Simulation.StackSpace.SkipAffine
