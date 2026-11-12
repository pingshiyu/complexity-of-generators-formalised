import ComplexityOfGenerators.Simulation.ExactRecursive.Trial
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem counter_bound (value : Fin 35) (different) (p : PolynomialBound)
    (s : Store B V) (n cap : ℕ) (sizes : StoreBound s cap) (index : (s 13).length = n)
    (base : n + 1 ≤ cap) (result : p n ≤ cap) :
    StoreBound ((counter B V value different p).eval s) cap ∧
      (counter B V value different p).cost s ≤ 26 * cap + 7 + Command.counterBudget p n := by
  exact BoundedSource.counter_bound (O := α) (Symbol.unit : Cell B V) Symbol.bit value different p
    s n cap sizes index base result

theorem trialSetup_bound (seed time : PolynomialBound) (s : Store B V) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length = n) (empty : s 14 = [])
    (base : n + 1 ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap) :
    StoreBound (trialPrepared B V seed time s) cap ∧
      (trialSetup B V seed time).cost s ≤
        61 * cap + 20 + Command.counterBudget seed n + Command.counterBudget time n := by
  exact BoundedSource.trialSetup_bound (O := α) (Symbol.unit : Cell B V) Symbol.bit seed time
    s n cap sizes index empty base seedBound timeBound

theorem sourceTrial_bound {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (retract : Function.LeftInverse decode encode)
    (f g b : Cell B V → Cell B V) (bitCode : ∀ bit, b (.bit bit) = encode (.bit bit))
    (seed time : PolynomialBound) (s : Store B V) (data : InputData I A) (bits : BitString)
    (input_eq : (s 11).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s 12).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s 13).length = data.index) (random_eq : s 17 = bits.map Symbol.bit) (empty : s 14 = [])
    (cap : ℕ) (sizes : StoreBound s cap) (base : data.index + 1 ≤ cap)
    (seedBound : seed data.index ≤ cap) (timeBound : time data.index + 1 ≤ cap)
    (space : 1 + data.input.length + data.auxiliary.length + data.index + seed data.index +
      3 * (time data.index + 1) ≤ cap) :
    StoreBound ((sourceTrial B V M encode decode f g b seed time).eval s) cap ∧
      ((sourceTrial B V M encode decode f g b seed time).eval s 10).length ≤ time data.index + 1 ∧
      (sourceTrial B V M encode decode f g b seed time).cost s ≤
        ((Source.body M encode decode (Source.bank sourceSlots)).bound + 200) * (cap + 1) +
          Command.counterBudget seed data.index + Command.counterBudget time data.index := by
  exact BoundedSource.sourceTrial_bound (O := α) (Symbol.unit : Cell B V) Symbol.bit M encode decode retract f g b bitCode
    seed time s data bits input_eq auxiliary_eq index_eq random_eq empty
    cap sizes base seedBound timeBound space

end ComplexityOfGenerators.Simulation.ExactRecursive
