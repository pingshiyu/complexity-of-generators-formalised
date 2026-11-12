import ComplexityOfGenerators.Simulation.ExactRecursive.Program
import ComplexityOfGenerators.Simulation.WordStack.BoundedSource

namespace ComplexityOfGenerators.Simulation.ExactRecursive

/-! Compatibility wrappers around the shared bounded-source implementation. -/

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def trialSetup (seed time : PolynomialBound) : Controller B V :=
  (counter B V 18 (by decide) seed).seq
  ((Blocks.routine 18 17 14 (by decide) (by decide)).seq
  ((counter B V 16 (by decide) time).seq (WordStack.Routine.ofLocal (Local.push 16 .unit))))

def trialPrepared (seed time : PolynomialBound) (s : Store B V) : Store B V :=
  let n := (s 13).length
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update s 21 []) 19 (List.replicate (n + 1) .unit)) 20 []) 18 [])
        17 ((s 17).drop (seed n))) 14 (((s 17).take (seed n)).reverse ++ s 14))
    16 (List.replicate (time n + 1) .unit)

theorem trialSetup_eval (seed time : PolynomialBound) (s : Store B V) :
    (trialSetup B V seed time).eval s = trialPrepared B V seed time s := by
  exact BoundedSource.trialSetup_eval (O := α) (Symbol.unit : Cell B V) Symbol.bit seed time s

theorem sourceTrial_eval {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (f g b : Cell B V → Cell B V) (seed time : PolynomialBound) (s : Store B V) :
    (sourceTrial B V M encode decode f g b seed time).eval s =
      (Source.call (Output := α) M sourceSlots encode decode f g b).eval (trialPrepared B V seed time s) := by
  exact BoundedSource.sourceTrial_eval (O := α) (Symbol.unit : Cell B V) Symbol.bit M encode decode f g b seed time s

theorem sourceTrial_bank {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (retract : Function.LeftInverse decode encode)
    (f g b : Cell B V → Cell B V) (bitCode : ∀ bit, b (.bit bit) = encode (.bit bit))
    (seed time : PolynomialBound) (s : Store B V) (data : InputData I A) (bits : BitString)
    (input_eq : (s 11).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s 12).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s 13).length = data.index) (random_eq : s 17 = bits.map Symbol.bit) (empty : s 14 = []) :
    (sourceTrial B V M encode decode f g b seed time).eval s ∘ Source.bank sourceSlots =
      Local.mapStore encode (((Source.Snapshot.step M)^[time data.index + 1]
        (Source.initial M data (bits.take (seed data.index)))).store M) := by
  exact BoundedSource.sourceTrial_bank (O := α) (Symbol.unit : Cell B V) Symbol.bit M encode decode retract f g b bitCode
    seed time s data bits input_eq auxiliary_eq index_eq random_eq empty

theorem sourceTrial_outside {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (f g b : Cell B V → Cell B V) (seed time : PolynomialBound) (s : Store B V)
    (j : Fin 35) (outside : 11 ≤ j.val) (clock : j ≠ 16) :
    (sourceTrial B V M encode decode f g b seed time).eval s j =
      if j = 14 ∨ j = 15 then [] else trialPrepared B V seed time s j := by
  exact BoundedSource.sourceTrial_outside (O := α) (Symbol.unit : Cell B V) Symbol.bit M encode decode f g b
    seed time s j outside clock

theorem sourceTrial_result {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (retract : Function.LeftInverse decode encode)
    (f g b : Cell B V → Cell B V) (bitCode : ∀ bit, b (.bit bit) = encode (.bit bit))
    (seed time : PolynomialBound) (s : Store B V) (data : InputData I A) (bits : BitString)
    (input_eq : (s 11).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s 12).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s 13).length = data.index) (random_eq : s 17 = bits.map Symbol.bit) (empty : s 14 = []) :
    ∃ (status : Source.Status (Fin M.states)) (output : List α),
      (sourceTrial B V M encode decode f g b seed time).eval s 0 = [encode (.state status)] ∧
      (sourceTrial B V M encode decode f g b seed time).eval s 10 = output.map (fun a => encode (.output a)) ∧
      ∀ word, (status = .accepted ∧ output.reverse = word) ↔
        M.run data (bits.take (seed data.index)) (time data.index) = .halted (.accepted word) := by
  exact BoundedSource.sourceTrial_result (O := α) (Symbol.unit : Cell B V) Symbol.bit M encode decode retract f g b bitCode
    seed time s data bits input_eq auxiliary_eq index_eq random_eq empty

end ComplexityOfGenerators.Simulation.ExactRecursive
