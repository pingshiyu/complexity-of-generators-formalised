import ComplexityOfGenerators.Proofs.BinaryInputCorrectness

/-!
# Exhaustion of incomplete random inputs

The sampling routine terminates on every finite tape, including tapes ending
between a continuation flag and its digit. These operational facts complement
the successful-seed theorems; almost-sure sampling alone does not imply them.
-/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

/-- A missing stop flag or digit exhausts the native random tape in finite time. -/
theorem binary_input_digits_exhaust (data : InputData Unit Bool) (bits remaining : BitString)
    (family : Bool) (written : List RecursiveAlphabet) (consumed : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet (.flag family) written consumed c)
    (rest : bits.drop consumed = remaining) (incomplete : readBinaryDigits remaining = none) :
    ∃ t, (binaryInputMachine program control alphabet).runFrom data bits c t = .halted .exhausted := by
  let M := binaryInputMachine program control alphabet
  induction remaining using readBinaryDigits.induct generalizing written consumed c with
  | case1 tail => simp [readBinaryDigits] at incomplete
  | case2 bit tail ih =>
      have flag : bits[consumed]? = some true := by
        change bits[consumed + 0]? = some true
        rw [← List.getElem?_drop, rest]
        rfl
      have digit : bits[consumed + 1]? = some bit := by
        rw [← List.getElem?_drop, rest]
        rfl
      have later : bits.drop (consumed + 2) = tail := by
        simpa [List.drop_drop] using congrArg (fun xs : BitString => xs.drop 2) rest
      have unfinished : readBinaryDigits tail = none := by
        simpa [readBinaryDigits] using incomplete
      obtain ⟨selected, selectedReady, selection⟩ := binary_input_random program control alphabet data bits
        (.flag family) (.finish family) (.digit family) written consumed true c prepared flag rfl
      obtain ⟨read, readReady, reading⟩ := binary_input_random program control alphabet data bits
        (.digit family) (.write family false) (.write family true) written (consumed + 1) bit
        selected (by simpa using selectedReady) digit rfl
      obtain ⟨updated, updatedReady, update⟩ := binary_input_write program control alphabet data bits
        (.write family bit) (.flag family) written (consumed + 2) (stackLetter (binaryGlyph bit))
        read (by cases bit <;> simpa [Nat.add_assoc] using readReady) rfl
      obtain ⟨t, exhausted⟩ := ih (written ++ [stackLetter (binaryGlyph bit)]) (consumed + 2)
        updated updatedReady later unfinished
      refine ⟨1 + (1 + (1 + t)), ?_⟩
      exact (M.runFrom_add data bits c selected 1 selection (1 + (1 + t))).trans
        ((M.runFrom_add data bits selected read 1 reading (1 + t)).trans
          ((M.runFrom_add data bits read updated 1 update t).trans exhausted))
  | case3 remaining noStop noDigit =>
      cases remaining with
      | nil =>
          have missing : bits.length ≤ consumed := by
            have length := congrArg List.length rest
            simp only [List.length_drop, List.length_nil] at length
            omega
          exact ⟨0, binary_input_exhausts program control alphabet data bits
            (.flag family) (.finish family) (.digit family) written consumed c prepared missing rfl⟩
      | cons bit tail =>
          cases bit with
          | false => exact False.elim (noStop tail rfl)
          | true =>
              cases tail with
              | cons bit tail => exact False.elim (noDigit bit tail rfl)
              | nil =>
                  have flag : bits[consumed]? = some true := by
                    change bits[consumed + 0]? = some true
                    rw [← List.getElem?_drop, rest]
                    rfl
                  have missing : bits.length ≤ consumed + 1 := by
                    have length := congrArg List.length rest
                    simp only [List.length_drop, List.length_cons, List.length_nil] at length
                    omega
                  obtain ⟨d, ready, execution⟩ := binary_input_random program control alphabet data bits
                    (.flag family) (.finish family) (.digit family) written consumed true c prepared flag rfl
                  exact ⟨1, execution.trans (binary_input_exhausts program control alphabet data bits
                    (.digit family) (.write family false) (.write family true) written (consumed + 1)
                    d (by simpa using ready) missing rfl)⟩

/-- Failure to parse a number corresponds to exhaustion, never divergence. -/
theorem binary_input_number_exhaust (data : InputData Unit Bool) (bits remaining : BitString)
    (family : Bool) (written : List RecursiveAlphabet) (consumed : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet (.select family) written consumed c)
    (rest : bits.drop consumed = remaining) (incomplete : readBinaryNumber remaining = none) :
    ∃ t, (binaryInputMachine program control alphabet).runFrom data bits c t = .halted .exhausted := by
  let M := binaryInputMachine program control alphabet
  cases remaining with
  | nil =>
      have missing : bits.length ≤ consumed := by
        have length := congrArg List.length rest
        simp only [List.length_drop, List.length_nil] at length
        omega
      exact ⟨0, binary_input_exhausts program control alphabet data bits
        (.select family) (.finish family) (.write family true) written consumed c prepared missing rfl⟩
  | cons bit tail =>
      cases bit with
      | false => simp [readBinaryNumber] at incomplete
      | true =>
          have positive : bits[consumed]? = some true := by
            change bits[consumed + 0]? = some true
            rw [← List.getElem?_drop, rest]
            rfl
          have later : bits.drop (consumed + 1) = tail := by
            simpa [List.drop_drop] using congrArg (fun xs : BitString => xs.drop 1) rest
          have unfinished : readBinaryDigits tail = none := by
            simpa [readBinaryNumber] using incomplete
          obtain ⟨selected, selectedReady, selection⟩ := binary_input_random program control alphabet data bits
            (.select family) (.finish family) (.write family true) written consumed true c prepared positive rfl
          obtain ⟨updated, updatedReady, update⟩ := binary_input_write program control alphabet data bits
            (.write family true) (.flag family) written (consumed + 1) (stackLetter .bit1)
            selected (by simpa using selectedReady) rfl
          obtain ⟨t, exhausted⟩ := binary_input_digits_exhaust program control alphabet data bits tail family
            (written ++ [stackLetter .bit1]) (consumed + 1) updated updatedReady later unfinished
          exact ⟨1 + (1 + t), (M.runFrom_add data bits c selected 1 selection (1 + t)).trans
            ((M.runFrom_add data bits selected updated 1 update t).trans exhausted)⟩

/-- Every finite tape either contains two complete number samples, or the
actual native initialization exhausts it in finitely many transitions. -/
theorem binary_input_seed_cases (data : InputData Unit Bool) (bits : BitString) :
    (∃ candidate clock : ℕ, ∃ extra,
      bits = binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra) ∨
    (∃ t, (binaryInputMachine program control alphabet).run data bits t = .halted .exhausted) := by
  let M := binaryInputMachine program control alphabet
  obtain ⟨initial, initialReady, initialRun⟩ := binary_input_initial program control alphabet data bits
  rw [← M.runFrom_initial] at initialRun
  cases first : readBinaryNumber bits with
  | none =>
      obtain ⟨t, exhausted⟩ := binary_input_number_exhaust program control alphabet data bits bits false
        [stackBottom .cons] 0 initial initialReady (by simp) first
      exact Or.inr ⟨3 + t, by
        rw [← M.runFrom_initial]
        exact (M.runFrom_add data bits M.initialConfiguration initial 3 initialRun t).trans exhausted⟩
  | some pair =>
      obtain ⟨candidate, tail⟩ := pair
      have seed := readBinaryNumber_splits first
      cases second : readBinaryNumber tail with
      | some pair =>
          obtain ⟨clock, extra⟩ := pair
          exact Or.inl ⟨candidate, clock, extra, by
            rw [seed, readBinaryNumber_splits second, List.append_assoc]⟩
      | none =>
          have success := binary_input_number program control alphabet data bits false (candidate : Num)
            tail [stackBottom .cons] 0 initial initialReady (by simpa [binaryNumberSeed] using seed)
          norm_cast at success
          obtain ⟨firstTime, sampled, sampledReady, sampleRun⟩ := success
          obtain ⟨selected, selectedReady, selection⟩ := binary_input_write program control alphabet data bits
            (.finish false) (.select true)
            ([stackBottom .cons] ++ (PartrecToTM2.trNat candidate).reverse.map stackLetter)
            (binaryNumberSeed candidate).length (stackLetter .cons) sampled
            (by simpa [binaryNumberSeed] using sampledReady) rfl
          have later : bits.drop (binaryNumberSeed candidate).length = tail := by rw [seed]; simp
          obtain ⟨t, exhausted⟩ := binary_input_number_exhaust program control alphabet data bits tail true
            (([stackBottom .cons] ++ (PartrecToTM2.trNat candidate).reverse.map stackLetter) ++ [stackLetter .cons])
            (binaryNumberSeed candidate).length selected selectedReady later second
          refine Or.inr ⟨3 + (firstTime + (1 + t)), ?_⟩
          rw [← M.runFrom_initial]
          exact (M.runFrom_add data bits M.initialConfiguration initial 3 initialRun (firstTime + (1 + t))).trans
            ((M.runFrom_add data bits initial sampled firstTime sampleRun (1 + t)).trans
              ((M.runFrom_add data bits sampled selected 1 selection t).trans exhausted))

end

end ComplexityOfGenerators
