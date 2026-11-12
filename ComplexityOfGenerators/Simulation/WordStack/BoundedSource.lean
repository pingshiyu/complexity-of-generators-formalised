import ComplexityOfGenerators.Simulation.WordStack.SourceCall
import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
import ComplexityOfGenerators.Simulation.WordStack.Blocks
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

/-! A finite, clocked call to an arbitrary native source machine. Randomness
is consumed from a previously collected block, so calls can be composed while
retaining explicit primitive cost and support semantics. -/
namespace ComplexityOfGenerators.Simulation.WordStack.BoundedSource

variable {S O : Type} [Fintype S] (unitSymbol : S) (randomSymbol : Bool → S)

def sourceSlots : Source.Layout 35 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j eq; exact Fin.ext (congrArg (fun i : Fin 35 => i.val) eq)

@[simp] theorem sourceSlots_apply (i : Fin 17) : sourceSlots i = ⟨i.val, by omega⟩ := rfl

def counterSlots (value : Fin 35) (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21) :
    CounterRoutine.Layout 35 where
  toFun
    | 0 => 13
    | 1 => value
    | 2 => 19
    | 3 => 20
    | 4 => 21
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all [ne_comm]

@[simp] theorem counterSlots_apply (value : Fin 35)
    (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21) (i : Fin 5) :
    counterSlots value different i = match i with
      | 0 => 13 | 1 => value | 2 => 19 | 3 => 20 | 4 => 21 := rfl

def counter (_randomSymbol : Bool → S) (value : Fin 35) (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21)
    (p : PolynomialBound) : Routine S O 35 := CounterRoutine.routine (counterSlots value different) p unitSymbol

noncomputable def sourceTrial {I A : Type} (M : Machine I A O)
    (encode : Source.Symbol M → S) (decode : S → Source.Symbol M)
    (inputMap auxiliaryMap bitMap : S → S)
    (seed time : PolynomialBound) : Routine S O 35 :=
  (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).seq
  ((Blocks.routine 18 17 14 (by decide) (by decide)).seq
  ((counter (O := O) unitSymbol randomSymbol 16 (by decide) time).seq
  ((Routine.ofLocal (Local.push 16 unitSymbol)).seq
    (Source.call M sourceSlots encode decode inputMap auxiliaryMap bitMap))))

def trialSetup (seed time : PolynomialBound) : Routine S O 35 :=
  (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).seq
  ((Blocks.routine 18 17 14 (by decide) (by decide)).seq
  ((counter (O := O) unitSymbol randomSymbol 16 (by decide) time).seq (WordStack.Routine.ofLocal (Local.push 16 unitSymbol))))

def trialPrepared (_randomSymbol : Bool → S) (seed time : PolynomialBound) (s : Local.Store S 35) : Local.Store S 35 :=
  let n := (s 13).length
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update s 21 []) 19 (List.replicate (n + 1) unitSymbol)) 20 []) 18 [])
        17 ((s 17).drop (seed n))) 14 (((s 17).take (seed n)).reverse ++ s 14))
    16 (List.replicate (time n + 1) unitSymbol)

theorem trialSetup_eval (seed time : PolynomialBound) (s : Local.Store S 35) :
    (trialSetup (O := O) unitSymbol randomSymbol seed time).eval s = trialPrepared unitSymbol randomSymbol seed time s := by
  funext j
  fin_cases j <;>
    simp [trialSetup, trialPrepared, WordStack.Routine.seq, counter, CounterRoutine.routine_eval,
      Blocks.routine_eval (k := 35) 18 17 14 (by decide) (by decide) (by decide),
      WordStack.Routine.ofLocal, Local.eval_push, List.replicate_succ]

theorem sourceTrial_eval {I A : Type} (M : Machine I A O)
    (encode : Source.Symbol M → S) (decode : S → Source.Symbol M)
    (f g b : S → S) (seed time : PolynomialBound) (s : Local.Store S 35) :
    (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s =
      (Source.call (Output := O) M sourceSlots encode decode f g b).eval (trialPrepared unitSymbol randomSymbol seed time s) := by
  rw [← trialSetup_eval]
  rfl

theorem sourceTrial_bank {I A : Type} (M : Machine I A O)
    (encode : Source.Symbol M → S) (decode : S → Source.Symbol M)
    (retract : Function.LeftInverse decode encode)
    (f g b : S → S) (bitCode : ∀ bit, b (randomSymbol bit) = encode (.bit bit))
    (seed time : PolynomialBound) (s : Local.Store S 35) (data : InputData I A) (bits : BitString)
    (input_eq : (s 11).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s 12).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s 13).length = data.index) (random_eq : s 17 = bits.map randomSymbol) (empty : s 14 = []) :
    (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s ∘ Source.bank sourceSlots =
      Local.mapStore encode (((Source.Snapshot.step M)^[time data.index + 1]
        (Source.initial M data (bits.take (seed data.index)))).store M) := by
  rw [sourceTrial_eval]
  have result := Source.call_bank (Output := O) M sourceSlots encode decode retract f g b
    (trialPrepared unitSymbol randomSymbol seed time s) data (bits.take (seed data.index))
    (by simpa [trialPrepared] using input_eq)
    (by simpa [trialPrepared] using auxiliary_eq)
    (by simpa [trialPrepared] using index_eq)
    (by simp [trialPrepared, random_eq, empty, index_eq, List.map_take, List.map_map, Function.comp_def, bitCode])
  have clock : ((trialPrepared unitSymbol randomSymbol seed time s) (sourceSlots 16)).length = time data.index + 1 := by
    change ((trialPrepared unitSymbol randomSymbol seed time s) 16).length = _
    simp [trialPrepared, index_eq]
  simpa only [clock] using result

theorem sourceTrial_outside {I A : Type} (M : Machine I A O)
    (encode : Source.Symbol M → S) (decode : S → Source.Symbol M)
    (f g b : S → S) (seed time : PolynomialBound) (s : Local.Store S 35)
    (j : Fin 35) (outside : 11 ≤ j.val) (clock : j ≠ 16) :
    (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s j =
      if j = 14 ∨ j = 15 then [] else trialPrepared unitSymbol randomSymbol seed time s j := by
  rw [sourceTrial_eval]
  apply Source.call_frame
  · intro i equal
    have same := congrArg Fin.val equal
    change j.val = i.val at same
    omega
  · exact clock

theorem sourceTrial_result {I A : Type} (M : Machine I A O)
    (encode : Source.Symbol M → S) (decode : S → Source.Symbol M)
    (retract : Function.LeftInverse decode encode)
    (f g b : S → S) (bitCode : ∀ bit, b (randomSymbol bit) = encode (.bit bit))
    (seed time : PolynomialBound) (s : Local.Store S 35) (data : InputData I A) (bits : BitString)
    (input_eq : (s 11).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s 12).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s 13).length = data.index) (random_eq : s 17 = bits.map randomSymbol) (empty : s 14 = []) :
    ∃ (status : Source.Status (Fin M.states)) (output : List O),
      (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s 0 = [encode (.state status)] ∧
      (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s 10 = output.map (fun a => encode (.output a)) ∧
      ∀ word, (status = .accepted ∧ output.reverse = word) ↔
        M.run data (bits.take (seed data.index)) (time data.index) = .halted (.accepted word) := by
  let snapshot := (Source.Snapshot.step M)^[time data.index + 1]
    (Source.initial M data (bits.take (seed data.index)))
  have projection := sourceTrial_bank (O := O) unitSymbol randomSymbol M encode decode retract f g b bitCode seed time s data bits
    input_eq auxiliary_eq index_eq random_eq empty
  refine ⟨snapshot.status, snapshot.output, ?_, ?_, ?_⟩
  · have state := congrFun projection (0 : Fin 11)
    exact state
  · have output := congrFun projection (10 : Fin 11)
    change (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s 10 =
      (snapshot.output.map Source.Cell.output).map encode at output
    simpa only [List.map_map, Function.comp_def] using output
  · intro word
    constructor
    · rintro ⟨state, out⟩
      apply (Source.iterate_accept_iff M data (bits.take (seed data.index)) (time data.index) word).mp
      change snapshot.acceptedOutput = some word
      simp only [Source.Snapshot.acceptedOutput, state, out]
    · intro run
      obtain ⟨state, out⟩ := Source.iterate_accept M data (bits.take (seed data.index)) (time data.index) word run
      change snapshot.output = word.reverse at out
      exact ⟨state, by rw [out, List.reverse_reverse]⟩

theorem counter_bound (value : Fin 35) (different) (p : PolynomialBound)
    (s : Local.Store S 35) (n cap : ℕ) (sizes : StoreBound s cap) (index : (s 13).length = n)
    (base : n + 1 ≤ cap) (result : p n ≤ cap) :
    StoreBound ((counter (O := O) unitSymbol randomSymbol value different p).eval s) cap ∧
      (counter (O := O) unitSymbol randomSymbol value different p).cost s ≤ 26 * cap + 7 + Command.counterBudget p n := by
  constructor
  · apply sizes.counter (counterSlots value different) p unitSymbol
    · simpa [index] using base
    · simpa [index] using result
  · simpa [counter, index] using CounterRoutine.routine_cost
      (O := O) (counterSlots value different) p (unitSymbol) s cap sizes

theorem trialSetup_bound (seed time : PolynomialBound) (s : Local.Store S 35) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length = n) (empty : s 14 = [])
    (base : n + 1 ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap) :
    StoreBound (trialPrepared unitSymbol randomSymbol seed time s) cap ∧
      (trialSetup (O := O) unitSymbol randomSymbol seed time).cost s ≤
        61 * cap + 20 + Command.counterBudget seed n + Command.counterBudget time n := by
  let a := (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).eval s
  let b := (Blocks.routine (O := O) 18 17 14 (by decide) (by decide)).eval a
  let c := (counter (O := O) unitSymbol randomSymbol 16 (by decide) time).eval b
  obtain ⟨aBound, aCost⟩ := counter_bound (O := O) unitSymbol randomSymbol 18 (by decide) seed s n cap sizes index base seedBound
  have aIndex : (a 13).length = n := by simp [a, counter, CounterRoutine.routine_eval, index]
  have aEmpty : a 14 = [] := by simp [a, counter, CounterRoutine.routine_eval, empty]
  have bBound := aBound.block (O := O) 18 17 14 (by decide) (by decide) (by decide) aEmpty
  have bIndex : (b 13).length = n := by
    simp [b, Blocks.routine_eval (k := 35) 18 17 14 (by decide) (by decide) (by decide), aIndex]
  obtain ⟨cBound, cCost⟩ := counter_bound (O := O) unitSymbol randomSymbol 16 (by decide) time b n cap bBound bIndex base (by omega)
  have clock : (c 16).length = time n := by simp [c, counter, CounterRoutine.routine_eval, bIndex]
  constructor
  · rw [← trialSetup_eval]
    change StoreBound (Function.update c 16 (unitSymbol :: c 16)) cap
    exact cBound.update 16 _ (by simpa [clock] using timeBound)
  · have blocks := Blocks.routine_cost (O := O) (S := S) 18 17 14 (by decide) (by decide) a
    have clockSize : (a 18).length ≤ cap := aBound 18
    change (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).cost s + 1 +
      ((Blocks.routine 18 17 14 (by decide) (by decide)).cost a + 1 +
      ((counter (O := O) unitSymbol randomSymbol 16 (by decide) time).cost b + 1 +
      (WordStack.Routine.ofLocal (Local.push 16 unitSymbol)).cost c)) ≤ _
    simp only [WordStack.Routine.ofLocal, Local.push, Local.ticks] at *
    omega

theorem sourceTrial_bound {I A : Type} (M : Machine I A O)
    (encode : Source.Symbol M → S) (decode : S → Source.Symbol M)
    (retract : Function.LeftInverse decode encode)
    (f g b : S → S) (bitCode : ∀ bit, b (randomSymbol bit) = encode (.bit bit))
    (seed time : PolynomialBound) (s : Local.Store S 35) (data : InputData I A) (bits : BitString)
    (input_eq : (s 11).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s 12).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s 13).length = data.index) (random_eq : s 17 = bits.map randomSymbol) (empty : s 14 = [])
    (cap : ℕ) (sizes : StoreBound s cap) (base : data.index + 1 ≤ cap)
    (seedBound : seed data.index ≤ cap) (timeBound : time data.index + 1 ≤ cap)
    (space : 1 + data.input.length + data.auxiliary.length + data.index + seed data.index +
      3 * (time data.index + 1) ≤ cap) :
    StoreBound ((sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s) cap ∧
      ((sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).eval s 10).length ≤ time data.index + 1 ∧
      (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).cost s ≤
        ((Source.body M encode decode (Source.bank sourceSlots)).bound + 200) * (cap + 1) +
          Command.counterBudget seed data.index + Command.counterBudget time data.index := by
  let prepared := trialPrepared unitSymbol randomSymbol seed time s
  obtain ⟨setupBound, setupCost⟩ := trialSetup_bound (O := O) unitSymbol randomSymbol seed time s data.index cap sizes index_eq empty base seedBound timeBound
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
  · have projection := congrFun (sourceTrial_bank (O := O) unitSymbol randomSymbol M encode decode retract f g b bitCode seed time s data bits
        input_eq auxiliary_eq index_eq random_eq empty) (10 : Fin 11)
    have length := congrArg List.length projection
    simp only [Function.comp_apply, Local.mapStore, Source.Snapshot.store, List.length_map] at length
    exact length.trans_le (by
      simpa [Source.initial] using Source.Snapshot.iterate_output_length M
        (Source.initial M data (bits.take (seed data.index))) (time data.index + 1))
  · have callCost := Source.call_cost (Output := O) M sourceSlots encode decode f g b prepared cap setupBound
    have cost_eq : (sourceTrial (O := O) unitSymbol randomSymbol M encode decode f g b seed time).cost s =
        (trialSetup (O := O) unitSymbol randomSymbol seed time).cost s + 1 +
          (Source.call (Output := O) M sourceSlots encode decode f g b).cost prepared := by
      simp only [sourceTrial, trialSetup, WordStack.Routine.seq, trialSetup_eval]
      change _ = _
      simp only [trialSetup, WordStack.Routine.seq] at setupCost
      dsimp [prepared]
      rw [← trialSetup_eval]
      dsimp [trialSetup, WordStack.Routine.seq]
      omega
    rw [cost_eq]
    nlinarith

end ComplexityOfGenerators.Simulation.WordStack.BoundedSource
