import ComplexityOfGenerators.Simulation.WordCode

/-!
# Decoding a computed word inside the recursive program

The scalar word encoding is decoded into a list of symbol codes by an actual
library `Code` program. It returns the codes in reverse order, so the subsequent
native output routine can scan the stack representation from its bottom toward
its top and emit the original word in order.
-/

namespace ComplexityOfGenerators.Simulation

open Turing ToPartrec Encodable

set_option backward.isDefEq.respectTransparency false

private theorem exists_unpairCode : ∃ left right : Code, ∀ n : ℕ,
    left.eval [n] = Part.some [(Nat.unpair n).1] ∧
    right.eval [n] = Part.some [(Nat.unpair n).2] := by
  have leftPrimitive : Primrec (fun n : ℕ => (Nat.unpair n).1) := Primrec.fst.comp Primrec.unpair
  have rightPrimitive : Primrec (fun n : ℕ => (Nat.unpair n).2) := Primrec.snd.comp Primrec.unpair
  obtain ⟨left, leftCorrect⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr leftPrimitive.to_comp.partrec)
  obtain ⟨right, rightCorrect⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr rightPrimitive.to_comp.partrec)
  refine ⟨left, right, ?_⟩
  intro n
  exact ⟨leftCorrect (⟨[n], rfl⟩ : List.Vector ℕ 1), rightCorrect (⟨[n], rfl⟩ : List.Vector ℕ 1)⟩

noncomputable def unpairLeftCode : Code := exists_unpairCode.choose
noncomputable def unpairRightCode : Code := exists_unpairCode.choose_spec.choose

theorem unpairLeftCode_eval (n : ℕ) :
    unpairLeftCode.eval [n] = Part.some [(Nat.unpair n).1] :=
  (exists_unpairCode.choose_spec.choose_spec n).1

theorem unpairRightCode_eval (n : ℕ) :
    unpairRightCode.eval [n] = Part.some [(Nat.unpair n).2] :=
  (exists_unpairCode.choose_spec.choose_spec n).2

/-- The first number is the remaining word code; the following numbers are
the symbol codes decoded so far. A zero code stops the loop. -/
noncomputable def wordDecodeStep : Code :=
  .case .zero'
    (.cons (.comp .succ .zero)
      (.cons (.comp unpairRightCode .head) (.cons (.comp unpairLeftCode .head) .tail)))

theorem wordDecodeStep_stop (acc : List ℕ) :
    wordDecodeStep.eval (0 :: acc) = Part.some (0 :: acc) := by
  simp [wordDecodeStep]

theorem wordDecodeStep_next (letter tail : ℕ) (acc : List ℕ) :
    wordDecodeStep.eval ((Nat.pair letter tail + 1) :: acc) =
      Part.some (1 :: tail :: letter :: acc) := by
  simp [wordDecodeStep, Part.bind_eq_bind, unpairLeftCode_eval, unpairRightCode_eval]

noncomputable def wordDecodeCode : Code := .fix wordDecodeStep

/-- Decoding preserves zero-valued symbol codes and the empty word. The
statement uses the same standard list encoding as the input adapter. -/
theorem wordDecodeCode_eval {α : Type} [Encodable α] (word : List α) (acc : List ℕ) :
    wordDecodeCode.eval (encode word :: acc) = Part.some ((word.map encode).reverse ++ acc) := by
  apply Part.eq_some_iff.mpr
  induction word generalizing acc with
  | nil =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [wordDecodeStep_stop]
  | cons letter word ih =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨encode word :: encode letter :: acc, ?_, ?_⟩
      · change Sum.inr (encode word :: encode letter :: acc) ∈
          (wordDecodeStep.eval ((Nat.pair (encode letter) (encode word) + 1) :: acc)).map _
        simp [wordDecodeStep_next]
      · have recursive := ih (encode letter :: acc)
        change _ ∈ wordDecodeCode.eval (encode word :: encode letter :: acc)
        simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append] using recursive

theorem wordDecodeCode_word {α : Type} [Encodable α] (word : List α) :
    wordDecodeCode.eval [encode word] = Part.some (word.reverse.map encode) := by
  simpa using wordDecodeCode_eval word []

end ComplexityOfGenerators.Simulation
