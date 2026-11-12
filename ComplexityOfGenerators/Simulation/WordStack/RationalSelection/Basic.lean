import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Decode

/-!
Native bounded rational selection from a precollected Boolean block.
Input stacks 0,1,2 hold the unary denominator, numerator and coin block.
Stack 5 returns the decoded integer; 12 reports k<d and 13 reports k<a.
The comparison routines preserve both input unary words. At d=1 the decoder
consumes zero block bits. All control is implemented by primitive commands.
-/

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

def finish {O : Type} : Routine Bool O 16 :=
  (Compare.routine denominatorSlots true).seq (Compare.routine numeratorSlots true)

theorem finish_spec {O : Type} (s : Store) :
    (finish (O := O)).eval s 5 = s 5 ∧
    (finish (O := O)).eval s 12 = (if (s 5).length < (s 0).length then [true] else []) ∧
    (finish (O := O)).eval s 13 = (if (s 5).length < (s 1).length then [true] else []) ∧
    (finish (O := O)).eval s 2 = s 2 ∧ (finish (O := O)).eval s 0 = s 0 ∧
    (finish (O := O)).eval s 1 = s 1 := by
  simp [finish, Routine.seq, Compare.routine_eval, denominatorSlots, numeratorSlots]

def selector {O : Type} : Routine Bool O 16 := logRoutine.seq (decodeRoutine.seq finish)

theorem selector_spec {O : Type} (s : Store)
    (enough : Nat.clog 2 (s 0).length ≤ (s 2).length) :
    let b := Nat.clog 2 (s 0).length
    let value := FixedBitBlocks.decode ((s 2).take b)
    (selector (O := O)).eval s 5 = List.replicate value true ∧
    (selector (O := O)).eval s 12 = (if value < (s 0).length then [true] else []) ∧
    (selector (O := O)).eval s 13 = (if value < (s 1).length then [true] else []) ∧
    (selector (O := O)).eval s 2 = (s 2).drop b ∧
    (selector (O := O)).eval s 0 = s 0 ∧
    (selector (O := O)).eval s 1 = s 1 := by
  dsimp only
  simp only [selector, Routine.seq]
  let logged : Store := (logRoutine (O := O)).eval s
  let decoded : Store := (decodeRoutine (O := O)).eval logged
  have bitCount : logged 4 = List.replicate (Nat.clog 2 (s 0).length) true := (logRoutine_values s).2
  have originalBits : logged 2 = s 2 := logRoutine_input s 2 (by simp)
  have decodedValues := decodeRoutine_values (O := O) logged
    (by simpa [bitCount, originalBits] using enough)
  have number : decoded 5 = List.replicate
      (FixedBitBlocks.decode ((s 2).take (Nat.clog 2 (s 0).length))) true := by
    simpa [bitCount, originalBits] using decodedValues.2.1
  have remaining : decoded 2 = (s 2).drop (Nat.clog 2 (s 0).length) := by
    simpa [bitCount, originalBits] using decodedValues.2.2
  have denominator : decoded 0 = s 0 :=
    (decodeRoutine_input logged 0 (by simp)).trans (logRoutine_input s 0 (by simp))
  have numerator : decoded 1 = s 1 :=
    (decodeRoutine_input logged 1 (by simp)).trans (logRoutine_input s 1 (by simp))
  have finished := finish_spec (O := O) decoded
  refine ⟨finished.1.trans number, ?_, ?_, finished.2.2.2.1.trans remaining,
    finished.2.2.2.2.1.trans denominator, finished.2.2.2.2.2.trans numerator⟩
  · simpa only [number, denominator, List.length_replicate] using finished.2.1
  · simpa only [number, numerator, List.length_replicate] using finished.2.2.1

theorem selector_value_bound {O : Type} (s : Store)
    (enough : Nat.clog 2 (s 0).length ≤ (s 2).length) :
    ((selector (O := O)).eval s 5).length < 2 ^ Nat.clog 2 (s 0).length := by
  rw [(selector_spec s enough).1, List.length_replicate]
  have bound := FixedBitBlocks.decode_bound ((s 2).take (Nat.clog 2 (s 0).length))
  simpa [List.length_take, Nat.min_eq_left enough] using bound

theorem selector_one {O : Type} (s : Store) (denominator : (s 0).length = 1) :
    (selector (O := O)).eval s 5 = [] ∧
    (selector (O := O)).eval s 12 = [true] ∧
    (selector (O := O)).eval s 2 = s 2 := by
  have spec := selector_spec (O := O) s (by simp [denominator, Nat.clog_one_right])
  simp only [denominator, Nat.clog_one_right, List.take_zero, List.drop_zero,
    FixedBitBlocks.decode, List.replicate_zero, Nat.zero_lt_one, ite_true] at spec
  exact ⟨spec.1, spec.2.1, spec.2.2.2.1⟩

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
