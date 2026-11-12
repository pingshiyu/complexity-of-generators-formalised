import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Position
import ComplexityOfGenerators.Examples.HAMPATHFiniteChoices
import ComplexityOfGenerators.Examples.HAMPATHBaseGenerator

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse

set_option backward.isDefEq.respectTransparency false

def forcedRow (bits : List Bool) (start vertex : ℕ) : Bool :=
  if vertex = start then true else rowFromBits bits vertex

def value (graph : Graph) (start n : ℕ) (label : List Symbol) (bits : List Bool) : Option (List Symbol) :=
  if BaseSearch.Productive n then
    if label = [] then if graph.size = 1 then some (graph.encode start) else none
    else if encodingLength (graph.size+1) ≤ n then do
      let next ← decodeLabel (graph.size+1) label
      if width (graph.size+1)+2*graph.size ≤ bits.length then do
        let position ← Position.value graph.size start next
          (FixedBitBlocks.decode (bits.take (width (graph.size+1))))
        pure ((graph.insert position
          (rowFromBits ((bits.drop (width (graph.size+1))).take graph.size))
          (forcedRow ((bits.drop (width (graph.size+1)+graph.size)).take graph.size) start)).encode position)
      else none
    else none
  else none

theorem forcedRow_required (bits : List Bool) (start : ℕ) : forcedRow bits start start = true := by
  simp [forcedRow]

theorem value_sound (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (bits : List Bool) (word : List Symbol)
    (generated : value graph start n label bits = some word) :
    word ∈ selfReduction.inverseFibre n (graph.encode start) label := by
  by_cases productive : BaseSearch.Productive n
  · by_cases empty : label = []
    · by_cases singletonSize : graph.size = 1
      · have same : graph.encode start = word := by simpa [value, productive, empty, singletonSize] using generated
        obtain ⟨M, _, positive, rfl⟩ := productive
        rw [empty, inverseFibre_empty graph start member M]
        exact ⟨singletonSize, by omega, same.symm⟩
      · simp [value, productive, empty, singletonSize] at generated
    · by_cases capacity : encodingLength (graph.size+1) ≤ n
      · cases decoded : decodeLabel (graph.size+1) label with
        | none => simp [value, productive, empty, capacity, decoded] at generated
        | some next =>
            by_cases enough : width (graph.size+1)+2*graph.size ≤ bits.length
            · simp only [value, ite_eq_left productive, ite_eq_right empty, ite_eq_left capacity,
                decoded, Option.bind_eq_bind, Option.bind, ite_eq_left enough] at generated
              cases selected : Position.value graph.size start next
                  (FixedBitBlocks.decode (bits.take (width (graph.size+1)))) with
              | none => simp [selected] at generated
              | some position =>
                  simp only [selected, Option.bind_eq_bind, Option.bind, Option.pure_def,
                    Option.some.injEq] at generated
                  obtain ⟨positionBound, nextEq⟩ := Position.value_sound graph.size start next _ position
                    member.start_bound selected
                  obtain ⟨_, labelEq⟩ := decodeLabel_sound (graph.size+1) label next decoded
                  obtain ⟨M, _, _, rfl⟩ := productive
                  have sizeBound : graph.size+1 ≤ M := encodingLength_strictMono.le_iff_le.mp capacity
                  rw [inverseFibre_nonempty_label graph start member M label empty]
                  refine ⟨sizeBound, position,
                    rowFromBits ((bits.drop (width (graph.size+1))).take graph.size),
                    forcedRow ((bits.drop (width (graph.size+1)+graph.size)).take graph.size) start,
                    positionBound, forcedRow_required _ _, ?_, generated.symm⟩
                  rw [labelEq, nextEq]
            · simp [value, productive, empty, capacity, decoded, enough] at generated
      · simp [value, productive, empty, capacity] at generated
  · simp [value, productive] at generated

def witnessBits (graph : Graph) (position : ℕ) (incoming outgoing : ℕ → Bool) : List Bool :=
  FixedBitBlocks.encode (width (graph.size+1)) position ++
    rowBits graph.size incoming ++ rowBits graph.size outgoing

theorem witnessBits_length (graph : Graph) (position : ℕ) (incoming outgoing : ℕ → Bool) :
    (witnessBits graph position incoming outgoing).length = width (graph.size+1)+2*graph.size := by
  simp [witnessBits]
  omega

theorem witnessBits_parts (graph : Graph) (position : ℕ) (incoming outgoing : ℕ → Bool) :
    (witnessBits graph position incoming outgoing).take (width (graph.size+1)) =
        FixedBitBlocks.encode (width (graph.size+1)) position ∧
      ((witnessBits graph position incoming outgoing).drop (width (graph.size+1))).take graph.size =
        rowBits graph.size incoming ∧
      ((witnessBits graph position incoming outgoing).drop (width (graph.size+1)+graph.size)).take graph.size =
        rowBits graph.size outgoing := by
  have firstDrop : (FixedBitBlocks.encode (width (graph.size+1)) position).drop
      (width (graph.size+1)+graph.size) = [] := List.drop_eq_nil_iff.mpr (by simp)
  simp [witnessBits, List.take_append, List.drop_append, List.take_left', firstDrop]

theorem value_witness (graph : Graph) (start M position : ℕ)
    (member : HamiltonianFrom graph start) (capacity : graph.size+1 ≤ M)
    (positionBound : position ≤ graph.size) (incoming outgoing : ℕ → Bool)
    (required : outgoing start = true) :
    value graph start (encodingLength M) (vertexLabel (graph.size+1) (expand position start))
      (witnessBits graph position incoming outgoing) =
        some ((graph.insert position incoming outgoing).encode position) := by
  have positiveM : 1 ≤ M := by have := member.start_bound; omega
  have productive : BaseSearch.Productive (encodingLength M) :=
    ⟨M, by unfold encodingLength; omega, positiveM, rfl⟩
  have positiveWidth : 0 < width (graph.size+1) := by
    have large : 1 < graph.size+1 := by have := member.start_bound; omega
    exact Nat.clog_pos (by decide) large
  have nonempty : vertexLabel (graph.size+1) (expand position start) ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [vertexLabel_length, List.length_nil] at length
    omega
  have nextBound : expand position start < graph.size+1 := expand_lt member.start_bound
  have fits : position < 2^width (graph.size+1) :=
    (show position < graph.size+1 by omega).trans_le (Nat.le_pow_clog (by decide) _)
  obtain ⟨first, second, third⟩ := witnessBits_parts graph position incoming outgoing
  have chosen : Position.value graph.size start (expand position start)
      (FixedBitBlocks.decode ((witnessBits graph position incoming outgoing).take (width (graph.size+1)))) = some position := by
    rw [first, FixedBitBlocks.decode_encode _ _ fits]
    exact Position.value_complete graph.size start position member.start_bound positionBound
  have recovered : graph.insert position (rowFromBits (rowBits graph.size incoming))
      (forcedRow (rowBits graph.size outgoing) start) = graph.insert position incoming outgoing := by
    apply graph.insert_rows_congr position positionBound
    · intro vertex inside
      exact rowBits_lookup graph.size incoming vertex inside
    · intro vertex inside
      by_cases same : vertex = start
      · simp [forcedRow, same, required]
      · simp [forcedRow, same, rowBits_lookup graph.size outgoing vertex inside]
  simp only [value, if_pos productive, if_neg nonempty,
    if_pos (encodingLength_strictMono.monotone capacity), decodeLabel_encode nextBound,
    Option.bind_eq_bind, Option.bind, witnessBits_length, le_refl, ite_true, chosen,
    Option.pure_def, second, third, recovered]

theorem value_complete (graph : Graph) (start M : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (word : List Symbol)
    (supported : word ∈ selfReduction.inverseFibre (encodingLength M) (graph.encode start) label) :
    ∃ bits, bits.length ≤ width (graph.size+1)+2*graph.size ∧
      value graph start (encodingLength M) label bits = some word := by
  by_cases empty : label = []
  · subst label
    rw [inverseFibre_empty graph start member M] at supported
    obtain ⟨singletonSize, sizeBound, rfl⟩ := supported
    have productive : BaseSearch.Productive (encodingLength M) :=
      ⟨M, by unfold encodingLength; omega, by omega, rfl⟩
    exact ⟨[], by simp, by simp [value, productive, singletonSize]⟩
  · rw [inverseFibre_nonempty_label graph start member M label empty] at supported
    obtain ⟨capacity, position, incoming, outgoing, positionBound, required, rfl, rfl⟩ := supported
    exact ⟨witnessBits graph position incoming outgoing,
      (witnessBits_length _ _ _ _).le, value_witness graph start M position member capacity
        positionBound incoming outgoing required⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse
