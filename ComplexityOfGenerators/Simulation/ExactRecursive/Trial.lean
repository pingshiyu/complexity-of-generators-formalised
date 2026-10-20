import ComplexityOfGenerators.Simulation.ExactRecursive.Program

namespace ComplexityOfGenerators.Simulation.ExactRecursive

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
  funext j
  fin_cases j <;>
    simp [trialSetup, trialPrepared, WordStack.Routine.seq, counter, CounterRoutine.routine_eval,
      Blocks.routine_eval (k := 35) 18 17 14 (by decide) (by decide) (by decide),
      WordStack.Routine.ofLocal, Local.eval_push, List.replicate_succ]

theorem sourceTrial_eval {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (f g b : Cell B V → Cell B V) (seed time : PolynomialBound) (s : Store B V) :
    (sourceTrial B V M encode decode f g b seed time).eval s =
      (Source.call (Output := α) M sourceSlots encode decode f g b).eval (trialPrepared B V seed time s) := by
  rw [← trialSetup_eval]
  rfl

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
  rw [sourceTrial_eval]
  have result := Source.call_bank (Output := α) M sourceSlots encode decode retract f g b
    (trialPrepared B V seed time s) data (bits.take (seed data.index))
    (by simpa [trialPrepared] using input_eq)
    (by simpa [trialPrepared] using auxiliary_eq)
    (by simpa [trialPrepared] using index_eq)
    (by simp [trialPrepared, random_eq, empty, index_eq, List.map_take, List.map_map, Function.comp_def, bitCode])
  have clock : ((trialPrepared B V seed time s) (sourceSlots 16)).length = time data.index + 1 := by
    change ((trialPrepared B V seed time s) 16).length = _
    simp [trialPrepared, index_eq]
  simpa only [clock] using result

theorem sourceTrial_outside {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (f g b : Cell B V → Cell B V) (seed time : PolynomialBound) (s : Store B V)
    (j : Fin 35) (outside : 11 ≤ j.val) (clock : j ≠ 16) :
    (sourceTrial B V M encode decode f g b seed time).eval s j =
      if j = 14 ∨ j = 15 then [] else trialPrepared B V seed time s j := by
  rw [sourceTrial_eval]
  apply Source.call_frame
  · intro i equal
    have same := congrArg Fin.val equal
    change j.val = i.val at same
    omega
  · exact clock

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
  let snapshot := (Source.Snapshot.step M)^[time data.index + 1]
    (Source.initial M data (bits.take (seed data.index)))
  have projection := sourceTrial_bank B V M encode decode retract f g b bitCode seed time s data bits
    input_eq auxiliary_eq index_eq random_eq empty
  refine ⟨snapshot.status, snapshot.output, ?_, ?_, ?_⟩
  · have state := congrFun projection (0 : Fin 11)
    exact state
  · have output := congrFun projection (10 : Fin 11)
    change (sourceTrial B V M encode decode f g b seed time).eval s 10 =
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

end ComplexityOfGenerators.Simulation.ExactRecursive
