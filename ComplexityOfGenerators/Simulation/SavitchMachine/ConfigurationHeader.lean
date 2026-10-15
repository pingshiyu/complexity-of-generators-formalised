import ComplexityOfGenerators.Simulation.SavitchMachine.HeadComparison
import ComplexityOfGenerators.Foundations.SpaceCodeFields

/-! Connect the native header routines to the fields of the actual bounded
configuration encoding. The original input alphabet remains distinct from the
interpreter's bit and delimiter symbols. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationHeader

open StackSpace Frames
open Machine (HeaderField)
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

/-- A successful whole-configuration decode identifies exactly the unary
coordinate returned by the finite field-reading program. -/
theorem read_header (word : List I) (s : ℕ) (bits : List Bool)
    (code : M.SpaceCode (⟨word, [], word.length⟩ : InputData I A) s)
    (decoded : (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode bits = some code)
    (field : HeaderField) (answer : Bool) (saved : List (Alphabet I)) (r : ℕ)
    (bitsRoom : bits.length ≤ r) (savedRoom : saved.length ≤ r) (inputRoom : word.length ≤ r)
    (offsetRoom : field.offset M.states word.length ≤ r)
    (counterRoom : 2 * field.width M.states word.length s + 1 ≤ r) :
    Trace (ReadCoordinateAt.program (Alphabet.write (α := I)) (Alphabet.read (α := I))
      field.coefficient (field.constant M.states)) r
      (localConfig (.skip .copy) (carrying answer false)
        (ReadCoordinateAt.before Alphabet.write bits saved (field.width M.states word.length s) (Alphabet.input word)))
      (localConfig .done (carrying answer true)
        (ReadCoordinateAt.after Alphabet.write (M.spaceCodeHeader word s code field).val saved
          (field.width M.states word.length s) (Alphabet.input word))) := by
  have header := M.spaceCodeCodec_decode_header word s bits code decoded field
  obtain ⟨value, trace, _, exactValue⟩ := ReadCoordinateAt.run (Alphabet.write (α := I))
    (Alphabet.read (α := I)) Alphabet.inverse field.coefficient (field.constant M.states)
    answer bits saved (Alphabet.input word) (field.width M.states word.length s) r bitsRoom savedRoom
    (by simpa [Alphabet.input] using inputRoom) (by simpa [Alphabet.input, HeaderField.offset] using offsetRoom) counterRoom
  have actual : (FixedWidthCodec.fin (field.width M.states word.length s)).decode
      ((bits.drop (field.coefficient * (Alphabet.input word).length + field.constant M.states)).take
        (field.width M.states word.length s)) = some (M.spaceCodeHeader word s code field) := by
    simpa only [Alphabet.input, List.length_map, HeaderField.bits, HeaderField.offset] using header
  have valueEq := exactValue _ actual
  simpa only [actual, Option.isSome_some, valueEq] using trace

/-- Native comparison of a retained source coordinate with a field of a
valid target configuration. Invalid targets are handled by the more general
`HeadComparison.run`; this corollary exposes the graph's typed coordinates. -/
theorem compare_header (word : List I) (s : ℕ) (bits : List Bool)
    (code : M.SpaceCode (⟨word, [], word.length⟩ : InputData I A) s)
    (decoded : (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode bits = some code)
    (field : HeaderField) (source : Fin (field.width M.states word.length s))
    (direction : Move) (clamp answer : Bool) (r : ℕ)
    (bitsRoom : bits.length ≤ r) (inputRoom : word.length ≤ r)
    (offsetRoom : field.offset M.states word.length ≤ r)
    (counterRoom : 2 * field.width M.states word.length s + 1 ≤ r) :
    ∃ stk,
      Trace (HeadComparison.program (Alphabet.write (α := I)) (Alphabet.read (α := I))
        field.coefficient (field.constant M.states) direction clamp) r
        (localConfig (.read (.skip .copy)) (carrying answer false)
          (ReadCoordinateAt.before Alphabet.write bits ((unary source.val).map Alphabet.write)
            (field.width M.states word.length s) (Alphabet.input word)))
        (localConfig .done (carrying answer
          (decide (MoveCheck.destination direction clamp (field.width M.states word.length s - 1) source.val =
            some (M.spaceCodeHeader word s code field).val))) stk) ∧
      stk 6 = Alphabet.input word := by
  have header := M.spaceCodeCodec_decode_header word s bits code decoded field
  obtain ⟨stk, trace, preserved⟩ := HeadComparison.run (Alphabet.write (α := I))
    (Alphabet.read (α := I)) Alphabet.inverse field.coefficient (field.constant M.states)
    direction clamp answer bits (Alphabet.input word) source.val (field.width M.states word.length s) r
    source.isLt bitsRoom (by simpa [Alphabet.input] using inputRoom)
    (by simpa [Alphabet.input, HeaderField.offset] using offsetRoom) counterRoom
  have actual : (FixedWidthCodec.fin (field.width M.states word.length s)).decode
      ((bits.drop (field.coefficient * (Alphabet.input word).length + field.constant M.states)).take
        (field.width M.states word.length s)) = some (M.spaceCodeHeader word s code field) := by
    simpa only [Alphabet.input, List.length_map, HeaderField.bits, HeaderField.offset] using header
  exact ⟨stk, by simpa only [actual, Option.any_some] using trace, preserved⟩

end ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationHeader
