import ComplexityOfGenerators.Examples.HAMPATHNative.Width
import ComplexityOfGenerators.Examples.HAMPATHNative.LogarithmBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.StateBounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineWordFunction

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem widthCore_cost {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget)
    (sizes : StoreBound s budget) : (widthCore (O := O)).cost s ≤ 1100 * (budget + 1)^2 := by
  let a := (metadata (O := O)).eval s
  let b := (Logarithm.routine (O := O)).eval a
  have first := metadata_cost (O := O) s budget sizes
  have aBound : StoreBound a budget := metadata_bound s budget positive sizes
  have second := (Logarithm.routine_bound (O := O) a budget aBound).2
  have last := gate_cost (O := O) 19 b
  have length : (b 19).length ≤ budget := by
    rw [show b 19 = List.replicate (Nat.clog 2 (a 17).length) (.bit true) from Logarithm.routine_value a,
      List.length_replicate]
    exact (width_le_size (a 17).length).trans (aBound 17)
  change (metadata (O := O)).cost s + 1 +
    ((Logarithm.routine (O := O)).cost a + 1 + (gate (O := O) 19).cost b) ≤ _
  nlinarith only [first, second, last, length]

theorem wordWidth_le_length (word : List Symbol) : wordWidth word ≤ word.length := by
  rw [wordWidth_eq_header]
  split
  · exact (width_le_size (headerSize word)).trans (headerSize_le word)
  · omega

noncomputable def widthTime : PolynomialBound := PolynomialBound.ofPolynomial (2000 * (Polynomial.X + 2)^2)

theorem widthRoutine_time (word : List Symbol) (auxiliary : List Unit) :
    widthRoutine.cost (loaded word auxiliary).store + 1 +
      4 * (widthRoutine.eval (loaded word auxiliary).store 19).length ≤
      widthTime (word.length + auxiliary.length) := by
  let n := word.length + auxiliary.length
  let s := (prepared word auxiliary).store
  have first : prepare.cost (loaded word auxiliary).store = 6 * word.length := by
    simp [prepare, loaded, Routine.transfer]
  have parseCost := parser_cost (O := Unit) s n (prepared_sizes word auxiliary)
  have parseBound : StoreBound ((parser (O := Unit)).eval s) (n + 1) := parser_bound s n (prepared_sizes word auxiliary)
  have last := widthCore_cost (O := Unit) ((parser (O := Unit)).eval s) (n + 1) (by omega) parseBound
  have output := wordWidth_le_length word
  rw [widthRoutine_value, List.length_replicate]
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_pow]
  change prepare.cost (loaded word auxiliary).store + 1 +
    ((parser (O := Unit)).cost s + 1 + (widthCore (O := Unit)).cost ((parser (O := Unit)).eval s)) + 1 +
      4 * wordWidth word ≤ 2000 * (n + 2)^2
  rw [first]
  have inside : word.length ≤ n := by dsimp [n]; omega
  nlinarith only [parseCost, last, output, inside]

theorem widthRoutine_randomFree : Command.RandomFree widthRoutine.command := by
  simp [widthRoutine, widthCore, prepare, parser_randomFree, metadata_randomFree,
    Logarithm.routine_randomFree, gate_randomFree]

/-- The label width is computed by the actual bounded unary-logarithm
controller, after validating the complete graph encoding. -/
noncomputable def width_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => List.replicate (wordWidth word) ()) := by
  apply Routine.polynomialWordFunction widthRoutine 0 1 0 19 (by decide) id
    (fun (_ : Unit) => Symbol.bit false) (fun _ => some ())
    (fun word _ => List.replicate (wordWidth word) ()) widthTime widthRoutine_randomFree
  · intro word auxiliary
    have loadedEq : InputBank.loadedMemory (O := Unit) (0 : Fin 32) 1 (id : Symbol → Symbol)
        (fun (_ : Unit) => Symbol.bit false) ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) =
        loaded word auxiliary := by simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
    rw [loadedEq, widthRoutine_value]
    simp
  · intro word auxiliary
    have loadedEq : InputBank.loadedMemory (O := Unit) (0 : Fin 32) 1 (id : Symbol → Symbol)
        (fun (_ : Unit) => Symbol.bit false) ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) =
        loaded word auxiliary := by simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
    simpa only [loadedEq] using widthRoutine_time word auxiliary

end ComplexityOfGenerators.Examples.HAMPATH.Native
