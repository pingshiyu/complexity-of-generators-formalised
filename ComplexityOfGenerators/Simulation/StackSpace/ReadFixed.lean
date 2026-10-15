import ComplexityOfGenerators.Simulation.StackSpace.Transfer
import ComplexityOfGenerators.Foundations.FixedWidthCodecValidity

/-! Constant-width fields can be decoded by finite control alone. The width
is a property of the machine (for example its number of states or symbols),
not of its input. This routine reads one symbol per primitive instruction;
it does not use a stack-inspecting function as an oracle. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {Q V : Type} {k : ℕ}

/-- A finite decision tree for a fixed number of bits. The accumulator is
part of the program text, never an unbounded local register. -/
def readFixedCode (source : Fin (k + 1)) (success : List Bool → Q) (failure : Q) :
    ℕ → List Bool → Stmt (Option Bool) Q (V × Option (Option Bool)) k
  | 0, acc => .load (fun v => (v.1, none)) (.goto fun _ => success acc.reverse)
  | n + 1, acc => .pop source (fun v s => (v.1, s))
      (.branch (fun v => v.2.join.isSome)
        (.branch (fun v => v.2.join.getD false)
          (readFixedCode source success failure n (true :: acc))
          (readFixedCode source success failure n (false :: acc)))
        (.load (fun v => (v.1, none)) (.goto fun _ => failure)))

/-- A complete field is consumed in order, preserving its suffix and every
other register. The cache is cleared on return. -/
theorem readFixed_stepAux (source : Fin (k + 1)) (success : List Bool → Q) (failure : Q)
    (bits acc : List Bool) (suffix : List (Option Bool)) (v : V)
    (cache : Option (Option Bool)) (stk : Fin (k + 1) → List (Option Bool))
    (input : stk source = bits.map some ++ suffix) :
    TM2.stepAux (readFixedCode source success failure bits.length acc) (v, cache) stk =
      localConfig (success (acc.reverse ++ bits)) v (Function.update stk source suffix) := by
  induction bits generalizing stk acc cache with
  | nil =>
      have unchanged : Function.update stk source suffix = stk := by
        have eq : suffix = stk source := by simpa using input.symm
        rw [eq, Function.update_eq_self]
      simp [readFixedCode, TM2.stepAux, localConfig, unchanged]
  | cons bit bits ih =>
      have nextInput : (Function.update stk source (bits.map some ++ suffix)) source = bits.map some ++ suffix := by simp
      have next := ih (bit :: acc) (some (some bit))
        (Function.update stk source (bits.map some ++ suffix)) nextInput
      cases bit <;>
        simpa only [List.length_cons, readFixedCode, TM2.stepAux, input, List.map_cons,
          List.cons_append, List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
          Option.getD_some, Bool.cond_true, Bool.cond_false, List.reverse_cons,
          List.append_assoc, List.singleton_append, List.nil_append, Function.update_idem] using next

/-- An exhausted bitstream is rejected, rather than padded with zero bits. -/
theorem readFixed_short_stepAux (source : Fin (k + 1)) (success : List Bool → Q) (failure : Q)
    (bits acc : List Bool) (width : ℕ) (short : bits.length < width) (v : V)
    (cache : Option (Option Bool)) (stk : Fin (k + 1) → List (Option Bool))
    (input : stk source = bits.map some) :
    TM2.stepAux (readFixedCode source success failure width acc) (v, cache) stk =
      localConfig failure v (Function.update stk source []) := by
  induction bits generalizing width stk acc cache with
  | nil =>
      cases width with
      | zero => simp at short
      | succ width => simp [readFixedCode, TM2.stepAux, input, localConfig]
  | cons bit bits ih =>
      cases width with
      | zero => simp at short
      | succ width =>
          have next := ih (bit :: acc) width (by simpa using short)
            (some (some bit)) (Function.update stk source (bits.map some)) (by simp)
          cases bit <;>
            simpa only [readFixedCode, TM2.stepAux, input, List.map_cons, List.head?_cons,
              List.tail_cons, Option.join_some, Option.isSome_some, Option.getD_some,
              Bool.cond_true, Bool.cond_false, Function.update_idem] using next

/-- The fixed reader executes as one stack-machine source step. Its native
compilation still accounts for all primitive instructions in the decision tree. -/
theorem readFixed_trace (P : Q → Stmt (Option Bool) Q (V × Option (Option Bool)) k)
    (source : Fin (k + 1)) (entry : Q) (success : List Bool → Q) (failure : Q)
    (width : ℕ) (table : P entry = readFixedCode source success failure width [])
    (bits : List Bool) (v : V) (stk : Fin (k + 1) → List (Option Bool))
    (input : stk source = bits.map some) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig entry v stk)
      (localConfig (if width ≤ bits.length then success (bits.take width) else failure) v
        (Function.update stk source ((bits.drop width).map some))) := by
  have finalBound : ∀ j, ((Function.update stk source ((bits.drop width).map some)) j).length ≤ r := by
    intro j
    by_cases h : j = source
    · subst j
      have h := bound source
      simp only [input, List.length_map] at h
      simpa only [Function.update_self, List.length_map, List.length_drop] using (show bits.length - width ≤ r by omega)
    · simpa [Function.update_of_ne h] using bound j
  apply Trace.step (show Within r (localConfig entry v stk) from bound) ?_
    (.refl (localConfig (if width ≤ bits.length then success (bits.take width) else failure) v
      (Function.update stk source ((bits.drop width).map some))) finalBound)
  simp only [TM2.step, localConfig, table]
  congr 1
  by_cases enough : width ≤ bits.length
  · have splitInput : stk source = (bits.take width).map some ++ (bits.drop width).map some := by
      rw [← List.map_append, List.take_append_drop, input]
    have read := readFixed_stepAux source success failure (bits.take width) []
      ((bits.drop width).map some) v none stk splitInput
    simpa [List.length_take, Nat.min_eq_left enough, enough, localConfig] using read
  · have read := readFixed_short_stepAux source success failure bits [] width (by omega) v none stk input
    simpa [enough, List.drop_eq_nil_of_le (by omega : bits.length ≤ width), localConfig] using read

/-- Decode a machine-dependent constant-width field directly into a finite
continuation label. The decision tree is constructed from the fixed codec. -/
def readCodecCode {W : Type} (source : Fin (k + 1)) (codec : FixedWidthCodec W)
    (next : Option W → Q) : Stmt (Option Bool) Q (V × Option (Option Bool)) k :=
  readFixedCode source (next ∘ codec.decode) (next none) codec.width []

theorem readCodec_trace {W : Type}
    (P : Q → Stmt (Option Bool) Q (V × Option (Option Bool)) k)
    (source : Fin (k + 1)) (entry : Q) (codec : FixedWidthCodec W)
    (exact : codec.Exact) (next : Option W → Q)
    (table : P entry = readCodecCode source codec next)
    (bits : List Bool) (v : V) (stk : Fin (k + 1) → List (Option Bool))
    (input : stk source = bits.map some) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig entry v stk)
      (localConfig (next (codec.decode (bits.take codec.width))) v
        (Function.update stk source ((bits.drop codec.width).map some))) := by
  have trace := readFixed_trace P source entry (next ∘ codec.decode) (next none)
    codec.width table bits v stk input r bound
  by_cases enough : codec.width ≤ bits.length
  · simpa [enough] using trace
  · have short : (bits.take codec.width).length < codec.width := by simp; omega
    simpa [enough, exact.decode_short _ short] using trace

end ComplexityOfGenerators.Simulation.StackSpace
