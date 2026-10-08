import ComplexityOfGenerators.Proofs.GeometricSampling
import ComplexityOfGenerators.Simulation.OutputEncoding

/-!
# Sampling the library's canonical binary numbers

A first coin chooses zero or a positive number. A positive number begins with
a leading one, followed by continuation/digit pairs and a stop flag. Thus the
native input routine can write the canonical stack encoding one cell at a time,
without an arithmetic counter hidden in its finite transition table.
-/

namespace ComplexityOfGenerators

open Simulation Turing MeasureTheory

/-- Continuation flags and digits alternate; a false flag stops the number. -/
def readBinaryDigits : BitString → Option (List Bool × BitString)
  | false :: tail => some ([], tail)
  | true :: bit :: tail => (readBinaryDigits tail).map (fun p => (bit :: p.1, p.2))
  | _ => none

def binaryDigitSeed (digits : List Bool) : BitString :=
  digits.flatMap (fun bit => [true, bit]) ++ [false]

theorem readBinaryDigits_of_seed (digits : List Bool) (extra : BitString) :
    readBinaryDigits (binaryDigitSeed digits ++ extra) = some (digits, extra) := by
  induction digits with
  | nil => rfl
  | cons bit digits ih =>
      simpa [binaryDigitSeed, readBinaryDigits, List.append_assoc] using
        congrArg (Option.map (fun p : List Bool × BitString => (bit :: p.1, p.2))) ih

theorem readBinaryDigits_splits {bits digits tail : BitString}
    (parsed : readBinaryDigits bits = some (digits, tail)) :
    bits = binaryDigitSeed digits ++ tail := by
  induction bits using readBinaryDigits.induct generalizing digits tail with
  | case1 rest =>
      simp only [readBinaryDigits, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      rfl
  | case2 bit rest ih =>
      cases h : readBinaryDigits rest with
      | none => simp [readBinaryDigits, h] at parsed
      | some p =>
          simp only [readBinaryDigits, h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
          obtain ⟨rfl, rfl⟩ := parsed
          rw [ih h]
          simp [binaryDigitSeed, List.append_assoc]
  | case3 => simp [readBinaryDigits] at parsed

theorem readBinaryDigits_append {bits digits tail : BitString}
    (parsed : readBinaryDigits bits = some (digits, tail)) (extra : BitString) :
    readBinaryDigits (bits ++ extra) = some (digits, tail ++ extra) := by
  rw [readBinaryDigits_splits parsed, List.append_assoc, readBinaryDigits_of_seed]

def appendBinaryDigit (n : PosNum) (bit : Bool) : PosNum :=
  if bit then n.bit1 else n.bit0

def binaryDigitsValue (digits : List Bool) : PosNum := digits.foldl appendBinaryDigit .one

def positiveDigits : PosNum → List Bool
  | .one => []
  | .bit0 n => positiveDigits n ++ [false]
  | .bit1 n => positiveDigits n ++ [true]

theorem binaryDigitsValue_positiveDigits (n : PosNum) : binaryDigitsValue (positiveDigits n) = n := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simpa [binaryDigitsValue, positiveDigits, List.foldl_append, appendBinaryDigit] using
        congrArg PosNum.bit0 ih
  | bit1 n ih =>
      simpa [binaryDigitsValue, positiveDigits, List.foldl_append, appendBinaryDigit] using
        congrArg PosNum.bit1 ih

theorem positiveDigits_foldl (digits : List Bool) (initial : PosNum) :
    positiveDigits (digits.foldl appendBinaryDigit initial) = positiveDigits initial ++ digits := by
  induction digits generalizing initial with
  | nil => simp
  | cons bit digits ih =>
      rw [List.foldl_cons, ih]
      cases bit <;> simp [appendBinaryDigit, positiveDigits, List.append_assoc]

theorem positiveDigits_binaryDigitsValue (digits : List Bool) :
    positiveDigits (binaryDigitsValue digits) = digits := by
  simpa [binaryDigitsValue, positiveDigits] using positiveDigits_foldl digits .one

def binaryGlyph (bit : Bool) : PartrecToTM2.Γ' := if bit then .bit1 else .bit0

theorem trPosNum_binaryDigits (digits : List Bool) (initial : PosNum) :
    (PartrecToTM2.trPosNum (digits.foldl appendBinaryDigit initial)).reverse =
      (PartrecToTM2.trPosNum initial).reverse ++ digits.map binaryGlyph := by
  induction digits generalizing initial with
  | nil => simp
  | cons bit digits ih =>
      rw [List.foldl_cons, ih]
      cases bit <;> simp [appendBinaryDigit, binaryGlyph, PartrecToTM2.trPosNum, List.append_assoc]

/-- The value and written binary digits agree exactly with Mathlib's encoding. -/
theorem trNat_binaryDigitsValue (digits : List Bool) :
    (PartrecToTM2.trNat (binaryDigitsValue digits : ℕ)).reverse =
      .bit1 :: digits.map binaryGlyph := by
  have canonical : ((binaryDigitsValue digits : ℕ) : Num) = Num.pos (binaryDigitsValue digits) :=
    PosNum.of_to_nat' _
  rw [PartrecToTM2.trNat, canonical]
  exact trPosNum_binaryDigits digits .one

def readBinaryNumber : BitString → Option (ℕ × BitString)
  | false :: tail => some (0, tail)
  | true :: tail => (readBinaryDigits tail).map (fun p => ((binaryDigitsValue p.1 : ℕ), p.2))
  | [] => none

def numSeed : Num → BitString
  | .zero => [false]
  | .pos n => true :: binaryDigitSeed (positiveDigits n)

def binaryNumberSeed (n : ℕ) : BitString := numSeed n

theorem readBinaryNumber_of_numSeed (n : Num) (extra : BitString) :
    readBinaryNumber (numSeed n ++ extra) = some ((n : ℕ), extra) := by
  cases n with
  | zero => rfl
  | pos n => simp [numSeed, readBinaryNumber, readBinaryDigits_of_seed, binaryDigitsValue_positiveDigits]

/-- Every natural number has a concrete finite seed, including zero. -/
theorem readBinaryNumber_of_seed (n : ℕ) (extra : BitString) :
    readBinaryNumber (binaryNumberSeed n ++ extra) = some (n, extra) := by
  have correct := readBinaryNumber_of_numSeed (n : Num) extra
  norm_cast at correct

theorem readBinaryNumber_splits {bits tail : BitString} {n : ℕ}
    (parsed : readBinaryNumber bits = some (n, tail)) : bits = binaryNumberSeed n ++ tail := by
  cases bits with
  | nil => simp [readBinaryNumber] at parsed
  | cons bit bits =>
      cases bit with
      | false =>
          simp only [readBinaryNumber, Option.some.injEq, Prod.mk.injEq] at parsed
          obtain ⟨rfl, rfl⟩ := parsed
          rfl
      | true =>
          cases digits : readBinaryDigits bits with
          | none => simp [readBinaryNumber, digits] at parsed
          | some p =>
              simp only [readBinaryNumber, digits, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
              obtain ⟨rfl, rfl⟩ := parsed
              rw [readBinaryDigits_splits digits]
              simp [binaryNumberSeed, numSeed, positiveDigits_binaryDigitsValue]

theorem readBinaryNumber_append {bits tail : BitString} {n : ℕ}
    (parsed : readBinaryNumber bits = some (n, tail)) (extra : BitString) :
    readBinaryNumber (bits ++ extra) = some (n, tail ++ extra) := by
  cases bits with
  | nil => simp [readBinaryNumber] at parsed
  | cons bit bits =>
      cases bit with
      | false => simpa [readBinaryNumber] using parsed
      | true =>
          cases digits : readBinaryDigits bits with
          | none => simp [readBinaryNumber, digits] at parsed
          | some p =>
              simp only [List.cons_append, readBinaryNumber]
              rw [readBinaryDigits_append digits extra]
              simp only [readBinaryNumber, digits, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at parsed
              obtain ⟨rfl, rfl⟩ := parsed
              rfl

theorem readBinaryDigits_of_stop (bits : BitString) (n : ℕ)
    (available : 2 * n < bits.length) (stop : bits[2 * n] = false) :
    ∃ digits tail, readBinaryDigits bits = some (digits, tail) := by
  induction n generalizing bits with
  | zero =>
      cases bits with
      | nil => simp at available
      | cons bit tail =>
          have first : bit = false := by simpa using stop
          subst bit
          exact ⟨[], tail, rfl⟩
  | succ n ih =>
      cases bits with
      | nil => simp at available
      | cons bit rest =>
          cases bit with
          | false => exact ⟨[], rest, rfl⟩
          | true =>
              cases rest with
              | nil => simp at available
              | cons digit rest =>
                  have bound : 2 * n < rest.length := by simp only [List.length_cons] at available; omega
                  have index : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
                  simp only [index, List.getElem_cons_succ] at stop
                  obtain ⟨digits, tail, parsed⟩ := ih rest bound stop
                  exact ⟨digit :: digits, tail, by simp [readBinaryDigits, parsed]⟩

theorem readBinaryNumber_of_stop (bits : BitString) (n : ℕ)
    (available : 1 + 2 * n < bits.length) (stop : bits[1 + 2 * n] = false) :
    ∃ value tail, readBinaryNumber bits = some (value, tail) := by
  cases bits with
  | nil => simp at available
  | cons bit rest =>
      cases bit with
      | false => exact ⟨0, rest, rfl⟩
      | true =>
          have bound : 2 * n < rest.length := by simp only [List.length_cons] at available; omega
          have index : 1 + 2 * n = 2 * n + 1 := by omega
          have stopped : rest[2 * n] = false := by simpa only [index, List.getElem_cons_succ] using stop
          obtain ⟨digits, tail, parsed⟩ := readBinaryDigits_of_stop rest n bound stopped
          exact ⟨(binaryDigitsValue digits : ℕ), tail, by simp [readBinaryNumber, parsed]⟩

/-- A stop in the interleaved flag subsequence supplies a finite successful
number sample. The offset may depend on preceding samples. -/
theorem readBinaryNumber_finite_at_offset (stream : BitStream)
    (stops : ∀ offset, ∃ n, stream (offset + 2 * n) = false) (offset : ℕ) :
    ∃ length value tail,
      readBinaryNumber (streamPrefix (fun i => stream (offset + i)) length) = some (value, tail) := by
  obtain ⟨n, stop⟩ := stops (offset + 1)
  let bits := streamPrefix (fun i => stream (offset + i)) (2 * n + 2)
  have bound : 1 + 2 * n < bits.length := by simp [bits]; omega
  have stopped : bits[1 + 2 * n] = false := by
    simpa [bits, streamPrefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stop
  obtain ⟨value, tail, parsed⟩ := readBinaryNumber_of_stop bits n bound stopped
  exact ⟨2 * n + 2, value, tail, parsed⟩

theorem readBinaryNumber_ae_finite_at_every_offset :
    ∀ᵐ stream ∂fairCoinMeasure, ∀ offset, ∃ length value tail,
      readBinaryNumber (streamPrefix (fun i => stream (offset + i)) length) = some (value, tail) := by
  filter_upwards [fairCoin_ae_stop_at_every_binary_offset] with stream stops
  exact readBinaryNumber_finite_at_offset stream stops

def binarySamplingEvent : Set BitStream :=
  {stream | ∃ candidate clock : ℕ,
    stream ∈ cylinder (binaryNumberSeed candidate ++ binaryNumberSeed clock)}

theorem measurableSet_binarySamplingEvent : MeasurableSet binarySamplingEvent := by
  have description : binarySamplingEvent = ⋃ candidate : ℕ, ⋃ clock : ℕ,
      cylinder (binaryNumberSeed candidate ++ binaryNumberSeed clock) := by
    ext stream
    simp [binarySamplingEvent]
  rw [description]
  exact MeasurableSet.iUnion fun candidate => MeasurableSet.iUnion fun clock => measurableSet_cylinder _

/-- The successive candidate and clock loops finish with probability one.
Their starting offsets need not be independent of the preceding bits. -/
theorem fairCoinMeasure_binarySamplingEvent : fairCoinMeasure binarySamplingEvent = 1 := by
  apply (mem_ae_iff_prob_eq_one measurableSet_binarySamplingEvent).mp
  filter_upwards [readBinaryNumber_ae_finite_at_every_offset] with stream samples
  obtain ⟨length, candidate, tail, parsed⟩ := samples 0
  have initial : binaryNumberSeed candidate <+: streamPrefix stream length := by
    refine ⟨tail, ?_⟩
    simpa using (readBinaryNumber_splits parsed).symm
  have first := mem_cylinder_of_prefix initial (stream_mem_prefix_cylinder stream length)
  obtain ⟨length', clock, tail', parsed'⟩ := samples (binaryNumberSeed candidate).length
  have later : binaryNumberSeed clock <+:
      streamPrefix (fun i => stream ((binaryNumberSeed candidate).length + i)) length' := by
    exact ⟨tail', (readBinaryNumber_splits parsed').symm⟩
  have second := mem_cylinder_of_prefix later
    (stream_mem_prefix_cylinder (fun i => stream ((binaryNumberSeed candidate).length + i)) length')
  exact ⟨candidate, clock, mem_cylinder_append first second⟩

end ComplexityOfGenerators
