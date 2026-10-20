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
  constructor
  · apply sizes.counter (counterSlots value different) p .unit
    · simpa [index] using base
    · simpa [index] using result
  · simpa [counter, index] using CounterRoutine.routine_cost
      (O := α) (counterSlots value different) p (Symbol.unit : Cell B V) s cap sizes

theorem trialSetup_bound (seed time : PolynomialBound) (s : Store B V) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length = n) (empty : s 14 = [])
    (base : n + 1 ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap) :
    StoreBound (trialPrepared B V seed time s) cap ∧
      (trialSetup B V seed time).cost s ≤
        61 * cap + 20 + Command.counterBudget seed n + Command.counterBudget time n := by
  let a := (counter B V 18 (by decide) seed).eval s
  let b := (Blocks.routine (O := α) 18 17 14 (by decide) (by decide)).eval a
  let c := (counter B V 16 (by decide) time).eval b
  obtain ⟨aBound, aCost⟩ := counter_bound B V 18 (by decide) seed s n cap sizes index base seedBound
  have aIndex : (a 13).length = n := by simp [a, counter, CounterRoutine.routine_eval, index]
  have aEmpty : a 14 = [] := by simp [a, counter, CounterRoutine.routine_eval, empty]
  have bBound := aBound.block (O := α) 18 17 14 (by decide) (by decide) (by decide) aEmpty
  have bIndex : (b 13).length = n := by
    simp [b, Blocks.routine_eval (k := 35) 18 17 14 (by decide) (by decide) (by decide), aIndex]
  obtain ⟨cBound, cCost⟩ := counter_bound B V 16 (by decide) time b n cap bBound bIndex base (by omega)
  have clock : (c 16).length = time n := by simp [c, counter, CounterRoutine.routine_eval, bIndex]
  constructor
  · rw [← trialSetup_eval]
    change StoreBound (Function.update c 16 (Symbol.unit :: c 16)) cap
    exact cBound.update 16 _ (by simpa [clock] using timeBound)
  · have blocks := Blocks.routine_cost (O := α) (S := Cell B V) 18 17 14 (by decide) (by decide) a
    have clockSize : (a 18).length ≤ cap := aBound 18
    change (counter B V 18 (by decide) seed).cost s + 1 +
      ((Blocks.routine 18 17 14 (by decide) (by decide)).cost a + 1 +
      ((counter B V 16 (by decide) time).cost b + 1 +
      (WordStack.Routine.ofLocal (Local.push 16 .unit)).cost c)) ≤ _
    simp only [WordStack.Routine.ofLocal, Local.push, Local.ticks] at *
    omega

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
  let prepared := trialPrepared B V seed time s
  obtain ⟨setupBound, setupCost⟩ := trialSetup_bound B V seed time s data.index cap sizes index_eq empty base seedBound timeBound
  have iEq : (prepared (sourceSlots 11)).map f = data.input.map (fun a => encode (.input a)) := by
    simpa [prepared, trialPrepared] using input_eq
  have aEq : (prepared (sourceSlots 12)).map g = data.auxiliary.map (fun a => encode (.auxiliary a)) := by
    simpa [prepared, trialPrepared] using auxiliary_eq
  have nEq : (prepared (sourceSlots 13)).length = data.index := by
    simpa [prepared, trialPrepared] using index_eq
  have rEq : (prepared (sourceSlots 14)).reverse.map b =
      (bits.take (seed data.index)).map (fun a => encode (.bit a)) := by
    simp [prepared, trialPrepared, random_eq, empty, index_eq, List.map_take, List.map_map, Function.comp_def, bitCode]
  have clock : (prepared (sourceSlots 16)).length = time data.index + 1 := by
    simp [prepared, trialPrepared, index_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceTrial_eval]
    apply Source.call_size_of_bound M sourceSlots encode decode retract f g b prepared data
      (bits.take (seed data.index)) iEq aEq nEq rEq cap setupBound
    rw [clock, List.length_take]
    omega
  · have projection := congrFun (sourceTrial_bank B V M encode decode retract f g b bitCode seed time s data bits
        input_eq auxiliary_eq index_eq random_eq empty) (10 : Fin 11)
    have length := congrArg List.length projection
    simp only [Function.comp_apply, Local.mapStore, Source.Snapshot.store, List.length_map] at length
    exact length.trans_le (by
      simpa [Source.initial] using Source.Snapshot.iterate_output_length M
        (Source.initial M data (bits.take (seed data.index))) (time data.index + 1))
  · have callCost := Source.call_cost (Output := α) M sourceSlots encode decode f g b prepared cap setupBound
    have cost_eq : (sourceTrial B V M encode decode f g b seed time).cost s =
        (trialSetup B V seed time).cost s + 1 +
          (Source.call (Output := α) M sourceSlots encode decode f g b).cost prepared := by
      simp only [sourceTrial, trialSetup, WordStack.Routine.seq, trialSetup_eval]
      change _ = _
      simp only [trialSetup, WordStack.Routine.seq] at setupCost
      dsimp [prepared]
      rw [← trialSetup_eval]
      dsimp [trialSetup, WordStack.Routine.seq]
      omega
    rw [cost_eq]
    nlinarith

end ComplexityOfGenerators.Simulation.ExactRecursive
