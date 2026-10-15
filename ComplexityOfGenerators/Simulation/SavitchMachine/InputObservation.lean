import ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt
import ComplexityOfGenerators.Simulation.StackSpace.ReadAt

/-! Check the input letter seen by an encoded configuration. Its input-head
field is parsed in bounded space, and a copy of the persistent input is scanned
at that unary position. No original input letter is collapsed to a bit. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.InputObservation

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [DecidableEq α]

inductive Label
  | read (pc : ReadCoordinateAt.Label) | copy | duplicate | scan | inspect | reject | done
  deriving DecidableEq, Fintype

def program (states : ℕ) (expected : Option α) : Label →
    Stmt (Alphabet α) Label (Status × Option (Alphabet α)) 6
  | .read .done => .branch (fun v => v.1.returned.getD false)
      (.goto fun _ => .copy) (.goto fun _ => .reject)
  | .read pc => embedCode (Function.Embedding.refl _) Label.read
      (ReadCoordinateAt.program Alphabet.write Alphabet.read 0 states pc)
  | .copy => transferCode 6 4 .copy .duplicate (fun _ => true)
  | .duplicate => duplicateCode 4 6 3 .duplicate .scan
  | .scan => readAtCode 3 0 .scan .inspect
  | .inspect => inspectCode 3
      (fun symbol status => {status with returned := some (decide (symbol = expected.map Sum.inl))}) .done
  | .reject => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)
  | .done => .halt

/-- Exact input-observation check, including rejection of invalid header
fields and the blank cell at the end of the read-only input. -/
theorem run (states : ℕ) (expected : Option α) (answer : Bool) (bits : List Bool)
    (word : List α) (r : ℕ) (bitsRoom : bits.length ≤ r) (inputRoom : word.length ≤ r)
    (offsetRoom : states ≤ r) (counterRoom : 2 * (word.length + 1) + 1 ≤ r) :
    ∃ stk,
      Trace (program states expected) r
        (localConfig (.read (.skip .copy)) (carrying answer false)
          (ReadCoordinateAt.before Alphabet.write bits [] (word.length + 1) (Alphabet.input word)))
        (localConfig .done (carrying answer
          (((FixedWidthCodec.fin (word.length + 1)).decode ((bits.drop states).take (word.length + 1))).any
            (fun head => decide ((word.drop head.val).head? = expected)))) stk) ∧
      stk 6 = Alphabet.input word := by
  let P := program states expected
  let field := (bits.drop states).take (word.length + 1)
  obtain ⟨value, parsed, valueBound, exactValue⟩ := ReadCoordinateAt.run (Alphabet.write (α := α))
    (Alphabet.read (α := α)) Alphabet.inverse 0 states answer bits [] (Alphabet.input word) (word.length + 1) r
    bitsRoom (by simp) (by simpa [Alphabet.input] using inputRoom) (by simpa using offsetRoom) counterRoom
  simp only [Nat.zero_mul, Nat.zero_add] at parsed exactValue
  have first := parsed.rename_active (by simp [localConfig]) Label.read P (by
    intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, localConfig, Option.map_some] at first
  let parsedMemory := ReadCoordinateAt.after (Alphabet.write (α := α)) value [] (word.length + 1) (Alphabet.input word)
  change Trace P r _ (localConfig (.read .done)
    (carrying answer ((FixedWidthCodec.fin (word.length + 1)).decode field).isSome) parsedMemory) at first
  cases decoded : (FixedWidthCodec.fin (word.length + 1)).decode field with
  | none =>
      simp only [decoded, Option.isSome_none] at first
      refine ⟨parsedMemory, ?_, rfl⟩
      simp only [Option.any_none]
      exact first.trans (.step first.end_bound rfl
        (.step first.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying]) (.refl _ first.end_bound)))
  | some head =>
      have valueEq := exactValue head decoded
      subst value
      simp only [decoded, Option.isSome_some] at first
      have ready : TM2.step P (localConfig (.read .done) (carrying answer true) parsedMemory) =
          some (localConfig .copy (carrying answer true) parsedMemory) := rfl
      have copied := copy_all P 4 6 3 .duplicate .scan .copy rfl rfl (by decide) (by decide) (by decide)
        (carrying answer true) parsedMemory rfl r first.end_bound (by
          simpa [parsedMemory, ReadCoordinateAt.after, Alphabet.input] using inputRoom)
      let withInput : Fin 7 → List (Alphabet α) :=
        ![(unary head.val).map Alphabet.write, [], (unary (word.length + 1)).map Alphabet.write,
          Alphabet.input word, [], [], Alphabet.input word]
      have copyLayout : Function.update parsedMemory (3 : Fin 7) (parsedMemory 6 ++ parsedMemory 3) = withInput := by
        funext j; fin_cases j <;> simp [parsedMemory, ReadCoordinateAt.after, withInput]
      rw [copyLayout] at copied
      have read := readAt_trace P 3 0 (by decide) .scan .inspect rfl .done
        (fun symbol status => {status with returned := some (decide (symbol = expected.map Sum.inl))}) rfl
        (carrying answer true) withInput r copied.end_bound
      have seen : (decide (((withInput 3).drop (withInput 0).length).head? = expected.map Sum.inl)) =
          decide ((word.drop head.val).head? = expected) := by
        have injective : Function.Injective (fun value : Option α => value.map (Sum.inl : α → Alphabet α)) := by
          intro a b same
          cases a <;> cases b <;> simpa using same
        change decide (((Alphabet.input word).drop ((unary head.val).map (Alphabet.write (α := α))).length).head? =
          expected.map Sum.inl) = decide ((word.drop head.val).head? = expected)
        simp only [Alphabet.input, List.length_map, List.length_replicate,
          ← List.map_drop, List.head?_map]
        simp only [injective.eq_iff]
      simp only [seen] at read
      refine ⟨replaceTwo withInput 3 0 ((withInput 3).drop (withInput 0).length) [], ?_, ?_⟩
      · simp only [Option.any_some]
        exact first.trans (.step first.end_bound ready (copied.trans read))
      · simp [replaceTwo, withInput]

end ComplexityOfGenerators.Simulation.SavitchMachine.InputObservation
