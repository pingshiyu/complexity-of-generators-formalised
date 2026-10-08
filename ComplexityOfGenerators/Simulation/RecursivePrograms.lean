import ComplexityOfGenerators.Simulation.StackMachine
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Partial-recursive programs compiled into native recognizers

This composes Mathlib's partial-recursive-code → TM2 → TM1 → Post simulations
with the verified finite-control compiler in this project. The input encoding
is stated explicitly; it is not confused with the unencoded word language in
Theorem 3.1. `WordInput` supplies the original-alphabet input adapter;
`RecursiveGenerator` composes random-bit reads and output emission.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

instance partrecStackFintype : Fintype PartrecToTM2.K' where
  elems := {.main, .rev, .aux, .stack}
  complete := by intro k; cases k <;> simp

/-- The fixed, finite alphabet used by the library's recursive-program compiler. -/
abbrev RecursiveAlphabet := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')

/-- Mathlib's explicit binary-and-delimiter encoding, then its stack-tape encoding. -/
def recursiveInput (input : List ℕ) : List RecursiveAlphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList input)

/-- Each recursive program has a genuine finite native transition table.
Acceptance on the encoded input is equivalent to definedness of the program. -/
theorem native_recognizer_of_recursive_code (code : ToPartrec.Code) :
    ∃ native : Machine RecursiveAlphabet Bool Unit, native.Deterministic ∧
      ∀ input bits, native.Accepts (decisionData (recursiveInput input)) bits ↔
        (code.eval input).Dom := by
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code .halt⟩
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_supported_tm2
    PartrecToTM2.tr (PartrecToTM2.codeSupp code .halt) (PartrecToTM2.tr_supports code .halt)
  refine ⟨native, deterministic, ?_⟩
  intro input bits
  unfold recursiveInput
  rw [accepts PartrecToTM2.K'.main (PartrecToTM2.trList input) bits]
  have initial : TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input) =
      PartrecToTM2.init code input := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp
  change (StateTransition.eval (TM2.step PartrecToTM2.tr)
    (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input))).Dom ↔ _
  rw [initial, PartrecToTM2.tr_eval]
  rfl

/-- Reuses Mathlib's equivalence of its unary and vector partial-recursive
bases, rather than introducing a second recursive-program datatype. -/
theorem native_recognizer_of_partrec {f : ℕ →. ℕ} (recursive : Partrec f) :
    ∃ native : Machine RecursiveAlphabet Bool Unit, native.Deterministic ∧
      ∀ n bits, native.Accepts (decisionData (recursiveInput [n])) bits ↔ (f n).Dom := by
  obtain ⟨code, specification⟩ :=
    ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr recursive)
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_recursive_code code
  refine ⟨native, deterministic, ?_⟩
  intro n bits
  rw [accepts [n] bits]
  let input : List.Vector ℕ 1 := ⟨[n], rfl⟩
  have correct := specification input
  change code.eval [n] = (fun value : ℕ => [value]) <$> f n at correct
  rw [correct]
  rfl

end ComplexityOfGenerators.Simulation
