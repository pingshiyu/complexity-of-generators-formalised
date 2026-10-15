import ComplexityOfGenerators.Foundations.FixedWidthCodec
import ComplexityOfGenerators.Foundations.FiniteReachability
import Complexitylib.Classes.Containments.Internal.SavitchSim

/-!
# Complexitylib's Savitch stack on an encoded finite graph

The midpoint counter, stack evaluator, termination proof, and encoded stack
bound come from Complexitylib. This module connects their semantics to our
bounded-path relation. Invalid vertex encodings cannot introduce paths.

This is a bound on the represented stack, not yet a visited-cell bound for a
native machine implementing the base tests and stack operations.
-/

namespace ComplexityOfGenerators.SavitchStack

open Complexity FiniteReachability

variable {V : Type} (codec : FixedWidthCodec V)

def zeroCode : List Bool := List.replicate codec.width false

@[simp] theorem zeroCode_length : (zeroCode codec).length = codec.width := by
  simp [zeroCode]

@[simp] theorem zeroCode_value : binValLE (zeroCode codec) = 0 :=
  binValLE_replicate_false _

variable (edge : V → V → Prop) (accept : V → Prop)
variable (br : List Bool → List Bool → Bool) (ba : List Bool → Bool)

/-- The reachability base test checks a path of zero or one edge, rejecting
invalid encodings. -/
def ReachBaseCorrect : Prop := ∀ u v, br u v = true ↔
  ∃ a b, codec.decode u = some a ∧ codec.decode v = some b ∧ Within edge 1 a b

/-- An acceptance leaf tests its current vertex. The combined recursion
covers `2^depth - 1` edges; the reachability leaves still cover one edge. -/
def AcceptBaseCorrect : Prop := ∀ u, ba u = true ↔
  ∃ a, codec.decode u = some a ∧ accept a

theorem reach_correct (base : ReachBaseCorrect codec edge br) (depth : ℕ)
    (u v : List Bool) :
    Sav.rchB br (zeroCode codec) depth u v = true ↔
      ∃ a b, codec.decode u = some a ∧ codec.decode v = some b ∧
        Within edge (2 ^ depth) a b := by
  induction depth generalizing u v with
  | zero => simpa [Sav.rchB] using base u v
  | succ depth ih =>
      rw [Sav.rchB]
      constructor
      · intro found
        obtain ⟨i, _, halves⟩ := Sav.exists_of_anyMid found
        simp only [Bool.and_eq_true] at halves
        obtain ⟨left, right⟩ := halves
        obtain ⟨a, mid, hu, hm, left⟩ := (ih _ _).mp left
        obtain ⟨mid', b, hm', hv, right⟩ := (ih _ _).mp right
        have same : mid = mid' := Option.some.inj (hm.symm.trans hm')
        subst mid'
        refine ⟨a, b, hu, hv, ?_⟩
        rw [pow_succ, Nat.mul_two, within_add]
        exact ⟨mid, left, right⟩
      · rintro ⟨a, b, hu, hv, path⟩
        rw [pow_succ, Nat.mul_two, within_add] at path
        obtain ⟨mid, left, right⟩ := path
        apply Sav.anyMid_of_length (w := codec.encode mid) (zeroCode_value codec)
          (by rw [codec.encode_length, zeroCode_length])
        rw [Bool.and_eq_true]
        exact ⟨(ih _ _).mpr ⟨a, mid, hu, codec.decode_encode mid, left⟩,
          (ih _ _).mpr ⟨mid, b, codec.decode_encode mid, hv, right⟩⟩

theorem accept_correct (reachBase : ReachBaseCorrect codec edge br)
    (acceptBase : AcceptBaseCorrect codec accept ba) (depth : ℕ) (u : List Bool) :
    Sav.accB br ba (zeroCode codec) depth u = true ↔
      ∃ a b, codec.decode u = some a ∧ Within edge (2 ^ depth - 1) a b ∧ accept b := by
  induction depth generalizing u with
  | zero => simpa [Sav.accB, Within] using acceptBase u
  | succ depth ih =>
      have splitLength : 2 ^ (depth + 1) - 1 = 2 ^ depth + (2 ^ depth - 1) := by
        have positive : 0 < 2 ^ depth := pow_pos (by decide) _
        rw [pow_succ]
        omega
      rw [Sav.accB]
      constructor
      · intro found
        obtain ⟨i, _, halves⟩ := Sav.exists_of_anyMid found
        simp only [Bool.and_eq_true] at halves
        obtain ⟨left, right⟩ := halves
        obtain ⟨a, mid, hu, hm, left⟩ := (reach_correct codec edge br reachBase depth _ _).mp left
        obtain ⟨mid', b, hm', right, accepted⟩ := (ih _).mp right
        have same : mid = mid' := Option.some.inj (hm.symm.trans hm')
        subst mid'
        refine ⟨a, b, hu, ?_, accepted⟩
        rw [splitLength, within_add]
        exact ⟨mid, left, right⟩
      · rintro ⟨a, b, hu, path, accepted⟩
        rw [splitLength, within_add] at path
        obtain ⟨mid, left, right⟩ := path
        apply Sav.anyMid_of_length (w := codec.encode mid) (zeroCode_value codec)
          (by rw [codec.encode_length, zeroCode_length])
        rw [Bool.and_eq_true]
        exact ⟨(reach_correct codec edge br reachBase depth _ _).mpr
            ⟨a, mid, hu, codec.decode_encode mid, left⟩,
          (ih _).mpr ⟨mid, b, codec.decode_encode mid, right, accepted⟩⟩

/-- One acceptance frame; the depth is unary and the three vertex fields have
the same fixed width. -/
def root (depth : ℕ) (start : V) : Sav.Frm where
  kind := true
  ph := false
  lvl := List.replicate depth false
  u := codec.encode start
  v := zeroCode codec
  m := zeroCode codec

def initial (depth : ℕ) (start : V) : Sav.Sst :=
  ⟨false, false, none, [root codec depth start]⟩

def run (depth : ℕ) (start : V) (steps : ℕ) : Sav.Sst :=
  (Sav.step br ba (zeroCode codec))^[steps] (initial codec depth start)

/-- The library stack halts and returns precisely bounded-path acceptance.
This reuses `Sav.run_top`, rather than reproving the stack interpreter. -/
theorem run_correct (reachBase : ReachBaseCorrect codec edge br)
    (acceptBase : AcceptBaseCorrect codec accept ba) (depth : ℕ) (start : V) :
    ∃ steps ≤ Sav.runBound codec.width depth + 1,
      (∀ j < steps, (run codec br ba depth start j).done = false) ∧
      (run codec br ba depth start steps).done = true ∧
      ((run codec br ba depth start steps).ans = true ↔
        ∃ finish, Within edge (2 ^ depth - 1) start finish ∧ accept finish) := by
  have ok : Sav.FrmOk br (zeroCode codec) (root codec depth start) :=
    ⟨rfl, by simp [root]⟩
  obtain ⟨T, bound, before, final, _⟩ :=
    Sav.run_top br ba (zeroCode codec) (zeroCode_value codec) (root codec depth start) ok
  have value := Sav.frameVal_fresh br ba (zeroCode codec)
    (f := root codec depth start) (zeroCode_value codec) rfl
  simp only [root, ↓reduceIte, List.length_replicate] at value
  change Sav.frameVal br ba (zeroCode codec) (root codec depth start) =
    Sav.accB br ba (zeroCode codec) depth (codec.encode start) at value
  refine ⟨T + 1, ?_, ?_, ?_, ?_⟩
  · simpa [root] using Nat.add_le_add_right bound 1
  · intro j hj
    exact before j (by omega)
  · change ((Sav.step br ba (zeroCode codec))^[T + 1] _).done = true
    rw [initial, final]
  · change ((Sav.step br ba (zeroCode codec))^[T + 1] _).ans = true ↔ _
    rw [initial, final]
    simp only [value]
    rw [accept_correct codec edge accept br ba reachBase acceptBase]
    simp [codec.decode_encode]

/-- An explicit bound on the serialized interpreter state. -/
def encodedSizeBound (width depth : ℕ) : ℕ :=
  (depth + 1) * (2 * (2 * depth + 5 * width + 14) + 2) + 14

/-- Polynomial depth and vertex width give the quadratic stack bound used in
the divide-and-conquer argument. -/
theorem encodedSizeBound_le_square {width depth : ℕ} (bound : width ≤ depth) :
    encodedSizeBound width depth ≤ 44 * (depth + 1) ^ 2 := by
  unfold encodedSizeBound
  nlinarith

theorem run_encoded_length (depth : ℕ) (start : V) (steps : ℕ) :
    (encSst [] (run codec br ba depth start steps)).length ≤
      encodedSizeBound codec.width depth := by
  have initialSize : Sav.StkSize depth codec.width (initial codec depth start).stk := by
    simp [initial, root, Sav.StkSize, Sav.FrmSize, codec.encode_length]
  have size := Sav.iterate_stkSize br ba (zeroCode codec)
    (by simp : (zeroCode codec).length ≤ codec.width) steps _ initialSize
  simpa [encodedSizeBound, run] using encSst_length_le [] _ size

end ComplexityOfGenerators.SavitchStack
