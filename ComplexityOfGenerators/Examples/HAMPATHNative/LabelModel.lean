import ComplexityOfGenerators.Examples.HAMPATHNative.LabelBits
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelChecks
import ComplexityOfGenerators.Examples.HAMPATHWordReduction

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

def nextValue (size : ℕ) (label : List Symbol) : ℕ :=
  FixedBitBlocks.decode ((label.map readBit ++ List.replicate (width size) false).take (width size))

def validCandidate (size start : ℕ) (label : List Symbol) : Bool :=
  let next := nextValue size label
  label.all LabelChecks.isBit && decide (label.length = width size) &&
    decide (next < size) && decide (next ≠ start)

def candidate (size start : ℕ) (label : List Symbol) : Option ℕ :=
  if validCandidate size start label then some (nextValue size label) else none

theorem decodeBits_allBits (label : List Symbol) (bits : label.all LabelChecks.isBit = true) :
    decodeBits label = some (FixedBitBlocks.decode (label.map readBit)) := by
  induction label with
  | nil => rfl
  | cons head rest ih =>
      cases head with
      | separator => simp [LabelChecks.isBit] at bits
      | bit value =>
          have tail : rest.all LabelChecks.isBit = true := by simpa [LabelChecks.isBit] using bits
          simp [decodeBits, ih tail, FixedBitBlocks.decode, readBit]

theorem nextValue_of_decoded (size : ℕ) (label : List Symbol) (next : ℕ)
    (length : label.length = width size) (decoded : decodeBits label = some next) :
    nextValue size label = next := by
  obtain ⟨bits, rfl, value⟩ := decodeBits_sound label next decoded
  simpa [nextValue, ← length, List.map_map, Function.comp_def, readBit, List.take_left] using value

theorem candidate_eq_decodeLabel (size start : ℕ) (label : List Symbol) :
    candidate size start label = match decodeLabel size label with
      | none => none
      | some next => if next = start then none else some next := by
  cases decoded : decodeLabel size label with
  | none =>
      change candidate size start label = none
      unfold candidate validCandidate
      dsimp only
      split_ifs with good
      · have facts : label.all LabelChecks.isBit = true ∧ label.length = width size ∧
            nextValue size label < size ∧ nextValue size label ≠ start := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using good
        have bits := decodeBits_allBits label facts.1
        have value : nextValue size label = FixedBitBlocks.decode (label.map readBit) := by
          simpa [nextValue, ← facts.2.1, List.take_left] using (rfl :
            FixedBitBlocks.decode (label.map readBit) = FixedBitBlocks.decode (label.map readBit))
        have present : decodeLabel size label = some (nextValue size label) := by
          simp [decodeLabel, facts.2.1, bits, ← value, facts.2.2.1]
        rw [decoded] at present
        cases present
      · rfl
  | some next =>
      change candidate size start label = if next = start then none else some next
      obtain ⟨bound, equal⟩ := decodeLabel_sound size label next decoded
      have length : label.length = width size := by rw [equal, vertexLabel_length]
      have number : decodeBits label = some next := by
        rw [equal, vertexLabel]
        apply decodeBits_encode
        exact bound.trans_le (Nat.le_pow_clog (by decide) size)
      have numeric := nextValue_of_decoded size label next length number
      have allBits : label.all LabelChecks.isBit = true := by
        rw [equal]
        simp [vertexLabel, encodeBits, LabelChecks.isBit]
      by_cases same : next = start <;> simp [candidate, validCandidate, numeric, allBits, length, bound, same]

theorem candidate_some_iff (size start : ℕ) (label : List Symbol) (next : ℕ) :
    candidate size start label = some next ↔ decodeLabel size label = some next ∧ next ≠ start := by
  rw [candidate_eq_decodeLabel]
  cases decoded : decodeLabel size label with
  | none => simp
  | some other =>
      by_cases same : other = start <;> simp_all
      intro equal found
      exact same (equal.trans found)

theorem wordReduce_candidate (graph : Graph) (start : ℕ) (inside : start < graph.size)
    (large : 2 ≤ graph.size) (label : List Symbol) :
    wordReduce (graph.encode start) label = match candidate graph.size start label with
      | none => []
      | some next => if graph.edge start next then (graph.delete start).encode (contract start next) else [] := by
  rw [candidate_eq_decodeLabel]
  cases decoded : decodeLabel graph.size label with
  | none => simp [wordReduce, decode_encode graph start inside, show ¬ graph.size ≤ 1 by omega, decoded]
  | some next =>
      by_cases same : next = start
      · simp [wordReduce, decode_encode graph start inside, show ¬ graph.size ≤ 1 by omega, decoded, same]
      · cases edge : graph.edge start next <;>
          simp [wordReduce, decode_encode graph start inside, show ¬ graph.size ≤ 1 by omega, decoded, same, edge]

end ComplexityOfGenerators.Examples.HAMPATH.Native
