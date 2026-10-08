import ComplexityOfGenerators.Simulation.RecursivePrograms
import Mathlib.Logic.Equiv.List

/-!
# Encoding a variable-length word inside the library machine

The recursive-program compiler accepts lists of natural numbers. This adapter
folds the reversed symbol codes into Mathlib's standard word encoding before
calling a unary program. It uses the library's actual `Code` instructions,
including its verified fixed-point semantics.
-/

namespace ComplexityOfGenerators.Simulation

open Turing ToPartrec Encodable

set_option backward.isDefEq.respectTransparency false

private theorem exists_consPairCode : ∃ code : Code, ∀ x acc : ℕ,
    code.eval [x, acc] = Part.some [Nat.pair x acc + 1] := by
  have primitive : Primrec (fun p : ℕ × ℕ => Nat.pair p.1 p.2 + 1) :=
    Primrec.succ.comp Primrec₂.natPair
  obtain ⟨code, specification⟩ :=
    Code.exists_code (Nat.Partrec'.part_iff₂.mpr primitive.to_comp.partrec.to₂)
  refine ⟨code, ?_⟩
  intro x acc
  exact specification (⟨[x, acc], rfl⟩ : List.Vector ℕ 2)

noncomputable def consPairCode : Code := exists_consPairCode.choose

theorem consPairCode_eval (x acc : ℕ) :
    consPairCode.eval [x, acc] = Part.some [Nat.pair x acc + 1] :=
  exists_consPairCode.choose_spec x acc

def firstTwo : Code := .cons .head (.cons (.comp .head .tail) .nil)

@[simp] theorem firstTwo_eval (x acc : ℕ) (tail : List ℕ) :
    firstTwo.eval (x :: acc :: tail) = Part.some [x, acc] := by simp [firstTwo, Part.bind_eq_bind]

def swapFirstTwo : Code := .cons (.comp .head .tail) (.cons .head (.comp .tail .tail))

@[simp] theorem swapFirstTwo_eval (x acc : ℕ) (tail : List ℕ) :
    swapFirstTwo.eval (acc :: x :: tail) = Part.some (x :: acc :: tail) := by
  simp [swapFirstTwo, Part.bind_eq_bind]

/-- The accumulator is first. A zero symbol terminates; a successor symbol
encodes one source letter. Each iteration removes that letter. -/
noncomputable def wordFoldStep : Code :=
  .comp (.case (.comp .zero' .head)
    (.cons (.comp .succ .zero) (.cons (.comp consPairCode firstTwo) (.comp .tail .tail))))
    swapFirstTwo

theorem wordFoldStep_stop (acc : ℕ) :
    wordFoldStep.eval [acc, 0] = Part.some [0, acc] := by
  simp [wordFoldStep]

theorem wordFoldStep_next (acc x : ℕ) (tail : List ℕ) :
    wordFoldStep.eval (acc :: (x + 1) :: tail) =
      Part.some (1 :: (Nat.pair x acc + 1) :: tail) := by
  simp [wordFoldStep, consPairCode_eval, Part.bind_eq_bind]

noncomputable def wordFoldCode : Code := .fix wordFoldStep

theorem wordFoldCode_eval (letters : List ℕ) (acc : ℕ) :
    wordFoldCode.eval (acc :: (letters.map Nat.succ ++ [0])) =
      Part.some [letters.foldl (fun a x => Nat.pair x a + 1) acc] := by
  apply Part.eq_some_iff.mpr
  induction letters generalizing acc with
  | nil =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [wordFoldStep_stop]
  | cons x letters ih =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨(Nat.pair x acc + 1) :: (letters.map Nat.succ ++ [0]), ?_, ih _⟩
      simp [wordFoldStep_next]

theorem word_fold_encoding {α : Type} [Encodable α] (word : List α) :
    (word.reverse.map encode).foldl (fun acc x => Nat.pair x acc + 1) 0 = encode word := by
  rw [List.map_reverse, List.foldl_reverse, List.foldr_map]
  induction word with
  | nil => rfl
  | cons letter word ih => simpa [Encodable.encodeList] using congrArg (fun n => Nat.pair (encode letter) n + 1) ih

/-- Variable-length symbol lists can now call an arbitrary unary recursive
program using exactly the standard encoding of their source word. -/
theorem wordFoldCode_word {α : Type} [Encodable α] (word : List α) :
    wordFoldCode.eval (0 :: ((word.reverse.map encode).map Nat.succ ++ [0])) =
      Part.some [encode word] := by
  rw [wordFoldCode_eval, word_fold_encoding]

/-- The arithmetic encoder can feed a compiled unary partial-recursive
recognizer from a variable-length list of letter codes. -/
theorem native_recognizer_of_word_codes {α : Type} [Encodable α]
    {f : ℕ →. ℕ} (recursive : Partrec f) :
    ∃ native : Machine RecursiveAlphabet Bool Unit, native.Deterministic ∧
      ∀ word : List α, ∀ bits,
        native.Accepts (decisionData (recursiveInput
          (0 :: ((word.reverse.map encode).map Nat.succ ++ [0])))) bits ↔
          (f (encode word)).Dom := by
  obtain ⟨code, specification⟩ :=
    Code.exists_code (Nat.Partrec'.part_iff₁.mpr recursive)
  obtain ⟨native, deterministic, accepts⟩ :=
    native_recognizer_of_recursive_code (.comp code wordFoldCode)
  refine ⟨native, deterministic, ?_⟩
  intro word bits
  rw [accepts]
  have correct := specification (⟨[encode word], rfl⟩ : List.Vector ℕ 1)
  change code.eval [encode word] = (fun n => [n]) <$> f (encode word) at correct
  change ((wordFoldCode.eval (0 :: ((word.reverse.map encode).map Nat.succ ++ [0]))).bind
    (fun input => code.eval input)).Dom ↔ (f (encode word)).Dom
  rw [wordFoldCode_word, Part.bind_some, correct]
  rfl

end ComplexityOfGenerators.Simulation
