import ComplexityOfGenerators.Simulation.WordCode
import ComplexityOfGenerators.Simulation.BlockRecognizer

/-! The original-word input adapter for the recursive-program compiler.
The stack encoding consists of a fixed leading marker, a fixed block for each
letter, and a fixed trailing accumulator. The concrete block loader reads the
ordinary input alphabet; the recursive encoder subsequently computes its
standard word code. -/

namespace ComplexityOfGenerators.Simulation

open Turing ToPartrec Encodable

set_option backward.isDefEq.respectTransparency false

def stackLetter (symbol : PartrecToTM2.Γ') : RecursiveAlphabet :=
  (false, Function.update (fun _ => none) PartrecToTM2.K'.main (some symbol))

def stackBottom (symbol : PartrecToTM2.Γ') : RecursiveAlphabet :=
  (true, Function.update (fun _ => none) PartrecToTM2.K'.main (some symbol))

def numberBlock (n : ℕ) : List RecursiveAlphabet :=
  (PartrecToTM2.trNat n ++ [PartrecToTM2.Γ'.cons]).reverse.map stackLetter

def wordBlocks (I : Type) [Encodable I] : InputBlocks I RecursiveAlphabet where
  leading := [stackBottom .cons]
  trailing := [stackLetter .cons]
  block := fun letter => numberBlock (encode letter + 1)

def wordNumbers {I : Type} [Encodable I] (word : List I) : List ℕ :=
  0 :: ((word.reverse.map encode).map Nat.succ ++ [0])

theorem trList_append (a b : List ℕ) :
    PartrecToTM2.trList (a ++ b) = PartrecToTM2.trList a ++ PartrecToTM2.trList b := by
  induction a with
  | nil => rfl
  | cons n a ih => simp [ih, List.append_assoc]

theorem trList_reverse_blocks {I : Type} (word : List I) (f : I → ℕ) :
    (PartrecToTM2.trList (word.reverse.map f)).reverse.map stackLetter =
      word.flatMap (fun letter => numberBlock (f letter)) := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        trList_append, List.reverse_append, List.map_append, List.flatMap_cons]
      rw [ih]
      rfl

/-- The block loader supplies exactly Mathlib's stack-machine initialization,
including the bottom marker, reversed letter order and terminal zero. -/
theorem wordBlocks_encoding {I : Type} [Encodable I] (word : List I) :
    (wordBlocks I).word word = recursiveInput (wordNumbers word) := by
  have reversed : (PartrecToTM2.trList (wordNumbers word)).reverse =
      PartrecToTM2.Γ'.cons ::
        ((PartrecToTM2.trList (word.reverse.map (fun letter => encode letter + 1))).reverse ++ [.cons]) := by
    simp [wordNumbers, trList_append, List.reverse_append, List.map_map, Function.comp_def, Nat.succ_eq_add_one]
  unfold recursiveInput TM2to1.trInit
  rw [reversed]
  dsimp only
  simp only [List.map_cons, List.map_append, List.map_nil, List.headI_cons, List.tail_cons]
  change stackBottom .cons :: (word.flatMap (fun letter => numberBlock (encode letter + 1)) ++ [stackLetter .cons]) =
    stackBottom .cons ::
      ((PartrecToTM2.trList (word.reverse.map (fun letter => encode letter + 1))).reverse.map stackLetter ++ [stackLetter .cons])
  rw [trList_reverse_blocks]

variable {I : Type} [Fintype I] [Encodable I]

theorem native_recognizer_of_recursive_code_words (code : Code) :
    ∃ native : Machine I Bool Unit, native.Deterministic ∧
      ∀ word bits, native.Accepts (decisionData word) bits ↔ (code.eval (wordNumbers word)).Dom := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_supported_tm1_blocks
    (TM2to1.tr PartrecToTM2.tr)
    (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp code .halt))
    (TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports code .halt)) (wordBlocks I)
  refine ⟨native, deterministic, ?_⟩
  intro word bits
  rw [accepts, wordBlocks_encoding, recursiveInput, TM2to1.tr_eval_dom]
  have initial : TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList (wordNumbers word)) =
      PartrecToTM2.init code (wordNumbers word) := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp
  change (StateTransition.eval (TM2.step PartrecToTM2.tr)
    (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList (wordNumbers word)))).Dom ↔ _
  rw [initial, PartrecToTM2.tr_eval]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Partial-recursive predicates on standard word encodings have genuine native
recognizers on ordinary words. No input-encoding hypothesis remains in this
theorem's acceptance specification. -/
theorem native_recognizer_of_partrec_words {f : ℕ →. ℕ} (recursive : Partrec f) :
    ∃ native : Machine I Bool Unit, native.Deterministic ∧
      ∀ word bits, native.Accepts (decisionData word) bits ↔ (f (encode word)).Dom := by
  obtain ⟨code, specification⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr recursive)
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_recursive_code_words (I := I) (.comp code wordFoldCode)
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
