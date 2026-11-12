import ComplexityOfGenerators.Examples.SATNative.EvaluationLoop
import ComplexityOfGenerators.Examples.SATNative.ParserModel

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open NativeAssignment

set_option backward.isDefEq.respectTransparency false

theorem binary_roundTrip (word : List Symbol) (binary : Binary word) :
    (word.map bitValue).map bitSymbol = word := by
  induction word with
  | nil => rfl
  | cons head rest ih =>
    have good := binary head (by simp)
    have tail := ih (by intro symbol member; exact binary symbol (by simp [member]))
    rcases good with rfl | rfl <;> simp [bitValue, bitSymbol, tail]

def finalState (word certificate : List Symbol) : State :=
  let header := NativeHeader.parsedState word
  (step (readOnes word).1 header.count certificate)^[header.word.length]
    (initial header.word header.valid)

def verifies (word certificate : List Symbol) : Bool :=
  if certificate.length = (NativeHeader.parsedState word).count ∧ Binary certificate then
    accepts (finalState word certificate)
  else false

theorem iterate_invalid (capacity active count : ℕ) (certificate : List Symbol) (state : State)
    (invalid : state.parserState.valid = false) :
    ((step capacity active certificate)^[count] state).parserState.valid = false := by
  induction count generalizing state with
  | zero => exact invalid
  | succ count ih => rw [Function.iterate_succ_apply]; exact ih _ (step_invalid capacity active certificate state invalid)

theorem verifies_sound (word certificate : List Symbol) (success : verifies word certificate = true) :
    certificate ∈ wordCertificates word := by
  unfold verifies at success
  split_ifs at success with certificateGood
  have headerValid : (NativeHeader.parsedState word).valid = true := by
    cases valid : (NativeHeader.parsedState word).valid with
    | true => rfl
    | false =>
      have bad := iterate_invalid (readOnes word).1 (NativeHeader.parsedState word).count
        (NativeHeader.parsedState word).word.length certificate
        (initial (NativeHeader.parsedState word).word (NativeHeader.parsedState word).valid) valid
      have impossible : (finalState word certificate).parserState.valid = false := bad
      simp [accepts, NativeBody.accepts, impossible] at success
  obtain ⟨capacity, bound, reconstruct⟩ := NativeHeader.parsedState_sound word headerValid
  have capacityEq : (readOnes word).1 = capacity := by rw [reconstruct, readOnes_header]
  let bits := certificate.map bitValue
  have bitLength : bits.length = (NativeHeader.parsedState word).count := by simpa [bits] using certificateGood.1
  have bitEncoding : bits.map bitSymbol = certificate := binary_roundTrip certificate certificateGood.2
  have bodySuccess : accepts
      ((step (readOnes word).1 (NativeHeader.parsedState word).count (bits.map bitSymbol))^[(NativeHeader.parsedState word).word.length]
        (initial (NativeHeader.parsedState word).word)) = true := by
    simpa [finalState, headerValid, bitEncoding] using success
  obtain ⟨formula, valid, satisfied, body⟩ := accepted_sound (by omega : (NativeHeader.parsedState word).count ≤ (readOnes word).1)
    bits bitLength (NativeHeader.parsedState word).word.length _ bodySuccess
  have equalBody : formula.bodyWord capacity = (NativeHeader.parsedState word).word := by
    rw [← capacityEq]
    exact body.symm
  have encoded : formula.encode capacity (NativeHeader.parsedState word).count = word := by
    calc
      formula.encode capacity (NativeHeader.parsedState word).count = List.replicate capacity .one ++
        .separator :: (List.replicate (NativeHeader.parsedState word).count .one ++
          List.replicate (capacity - (NativeHeader.parsedState word).count) .zero ++
            .separator :: formula.bodyWord capacity) := by
        simp [Formula.encode, Formula.bodyWord, List.append_assoc]
      _ = word := by rw [equalBody]; exact reconstruct.symm
  rw [← encoded, wordCertificates_encode bound formula valid]
  exact ⟨certificateGood.2, by simpa [certificates, bits] using And.intro bitLength satisfied⟩

theorem verifies_encode {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (certificate : List Symbol)
    (binary : Binary certificate) (length : certificate.length = active) :
    verifies (formula.encode capacity active) certificate = formula.eval (assignment (certificate.map bitValue)) := by
  have bitsLength : (certificate.map bitValue).length = active := by simpa using length
  have encoded := evaluate_encode bound (certificate.map bitValue) bitsLength formula valid _
    (NativeBody.tokenCount_bound bound formula valid)
  have header := NativeParser.header_encode capacity active bound formula
  simp only [verifies, header]
  simp only [length, binary, and_self, ite_true]
  simpa [finalState, header, NativeParser.capacity_encode, binary_roundTrip certificate binary] using encoded

theorem verifies_iff (word certificate : List Symbol) :
    verifies word certificate = true ↔ certificate ∈ wordCertificates word := by
  constructor
  · exact verifies_sound word certificate
  · intro member
    cases decoded : decode word with
    | none => simp [wordCertificates, decoded] at member
    | some triple =>
      rcases triple with ⟨capacity, active, formula⟩
      obtain ⟨bound, valid, equal⟩ := decode_sound word capacity active formula decoded
      have certificateGood : Binary certificate ∧ certificate.map bitValue ∈ certificates active formula := by
        simpa [wordCertificates, decoded] using member
      have length : certificate.length = active := by simpa using certificateGood.2.1
      rw [← equal, verifies_encode bound formula valid certificate certificateGood.1 length]
      exact certificateGood.2.2

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
