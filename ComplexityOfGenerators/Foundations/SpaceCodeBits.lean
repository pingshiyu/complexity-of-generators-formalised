import ComplexityOfGenerators.Foundations.SpaceSearch
import ComplexityOfGenerators.Foundations.SavitchStack

/-!
# Native configurations as inputs to the library Savitch stack

Configuration fields have a compositional, polynomial-width bit encoding.
The acceptance base tests the current instruction; reachability tests equality
or one of the two native successors. Neither enumerates all configurations.
-/

namespace ComplexityOfGenerators.Machine

set_option synthInstance.maxSize 4096

open FixedWidthCodec FiniteReachability

variable {I A O : Type} (M : Machine I A O)

/-- Control, three read-only heads, the work head, and the work window. -/
def spaceCodeCodec (data : InputData I A) (s : ℕ) : FixedWidthCodec (M.SpaceCode data s) :=
  (fin M.states).prod <| (fin (data.input.length + 1)).prod <|
    (fin (data.auxiliary.length + 1)).prod <| (fin (data.index + 1)).prod <|
      (fin (2 * s + 1)).prod <| (optionFin M.symbols).vector (2 * s + 1)

theorem spaceCodeCodec_width (data : InputData I A) (s : ℕ) :
    (M.spaceCodeCodec data s).width = M.spaceConfigurationExponent data s := by
  simp [spaceCodeCodec, prod, fin, optionFin, transport, spaceConfigurationExponent,
    Nat.add_assoc]

/-- Equality or one native edge, on decoded bitstrings. -/
def spaceReachBase (data : InputData I A) (s : ℕ) (u v : List Bool) : Bool :=
  match (M.spaceCodeCodec data s).decode u, (M.spaceCodeCodec data s).decode v with
  | some a, some b => decide (a = b ∨ M.SpaceCodeEdge data s a b)
  | _, _ => false

theorem spaceReachBase_correct (data : InputData I A) (s : ℕ) :
    SavitchStack.ReachBaseCorrect (M.spaceCodeCodec data s) (M.SpaceCodeEdge data s)
      (M.spaceReachBase data s) := by
  intro u v
  cases hu : (M.spaceCodeCodec data s).decode u <;>
    cases hv : (M.spaceCodeCodec data s).decode v <;>
    simp [spaceReachBase, hu, hv, Within]

/-- Test the current vertex's accepting instruction. With one-edge reachability
leaves, the recursion covers `2^depth - 1` edges, enough for every simple path. -/
def spaceAcceptBase (data : InputData I A) (s : ℕ) (u : List Bool) : Bool :=
  ((M.spaceCodeCodec data s).decode u).any (M.spaceCodeAccepting data s)

theorem spaceAcceptBase_correct (data : InputData I A) (s : ℕ) :
    SavitchStack.AcceptBaseCorrect (M.spaceCodeCodec data s)
      (fun a => M.spaceCodeAccepting data s a = true) (M.spaceAcceptBase data s) := by
  intro u
  simp [spaceAcceptBase, Option.any_eq_true]

/-- The library's concrete stack evaluator, instantiated with native graph
tests and the native initial configuration. -/
def spaceStackRun (data : InputData I A) (s depth steps : ℕ) : Complexity.Sav.Sst :=
  SavitchStack.run (M.spaceCodeCodec data s) (M.spaceReachBase data s)
    (M.spaceAcceptBase data s) depth (M.initialSpaceCode data s) steps

theorem SpaceBound.spaceStackRun_correct {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) (depth : ℕ)
    (large : M.spaceConfigurationExponent data s ≤ depth) :
    ∃ steps ≤ Complexity.Sav.runBound (M.spaceConfigurationExponent data s) depth + 1,
      (∀ j < steps, (M.spaceStackRun data s depth j).done = false) ∧
      (M.spaceStackRun data s depth steps).done = true ∧
      ((M.spaceStackRun data s depth steps).ans = true ↔ ∃ bits, M.Accepts data bits) := by
  obtain ⟨steps, bound, before, done, answer⟩ :=
    SavitchStack.run_correct (M.spaceCodeCodec data s) (M.SpaceCodeEdge data s)
      (fun a => M.spaceCodeAccepting data s a = true) (M.spaceReachBase data s)
      (M.spaceAcceptBase data s) (M.spaceReachBase_correct data s)
      (M.spaceAcceptBase_correct data s) depth (M.initialSpaceCode data s)
  rw [spaceCodeCodec_width] at bound
  refine ⟨steps, bound, before, done, answer.trans ?_⟩
  have cardinal : Fintype.card (M.SpaceCode data s) ≤ 2 ^ depth :=
    (M.spaceCode_card_le_two_pow data s).trans (Nat.pow_le_pow_right (by decide) large)
  have positive : 0 < 2 ^ depth := pow_pos (by decide) _
  have enough : Fintype.card (M.SpaceCode data s) ≤ (2 ^ depth - 1) + 1 := by omega
  simp only [← path_iff_within_pred (M.SpaceCodeEdge data s) (2 ^ depth - 1) enough]
  rw [M.spaceCode_acceptance_iff]
  exact (space.accepts_iff_boundedDecisionPath M).symm

theorem spaceStackRun_encoded_length (data : InputData I A) (s depth steps : ℕ) :
    (Complexity.encSst [] (M.spaceStackRun data s depth steps)).length ≤
      SavitchStack.encodedSizeBound (M.spaceConfigurationExponent data s) depth := by
  simpa [spaceStackRun, spaceCodeCodec_width] using
    SavitchStack.run_encoded_length (M.spaceCodeCodec data s) (M.spaceReachBase data s)
      (M.spaceAcceptBase data s) depth (M.initialSpaceCode data s) steps

end ComplexityOfGenerators.Machine
