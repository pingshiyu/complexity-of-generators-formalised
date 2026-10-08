import ComplexityOfGenerators.Simulation.WorkSteps
import ComplexityOfGenerators.Simulation.VirtualIndexSimulation
import Mathlib.Data.Fintype.Pi

/-!
# A finite bank of work tapes

This intermediate language accesses one selected work tape per instruction.
Its control, tape selector, and alphabet are finite. Reading, overwriting,
moving a head, and moving the physical input head each cost one instruction;
there are no operations on whole words or configurations in the instruction
set. The native compiler in `TapeBankCompiler` implements these instructions
on the original single work tape, with a quadratic time bound.
-/

namespace ComplexityOfGenerators.Simulation

inductive BankInstruction (Q S : Type)
  | accept | reject
  | step (next : Q) (write : S) (work input : Move)

/-- `origin` reports whether the selected virtual head is at position zero. -/
structure TapeBank (Q S : Type) (k : ℕ) where
  initial : Q
  blank : S
  select : Q → Fin k
  transition : Q → Option Bool → Bool → S → BankInstruction Q S

@[ext] structure BankConfiguration (Q S : Type) (k : ℕ) where
  state : Q
  inputHead : ℕ
  head : Fin k → ℤ
  tape : Fin k → ℤ → S

namespace TapeBank

variable {Q S : Type} {k : ℕ} (B : TapeBank Q S k)

def initialConfiguration : BankConfiguration Q S k :=
  ⟨B.initial, 0, fun _ => 0, fun _ _ => B.blank⟩

def instruction (word : BitString) (c : BankConfiguration Q S k) : BankInstruction Q S :=
  B.transition c.state word[c.inputHead]? (decide (c.head (B.select c.state) = 0))
    (c.tape (B.select c.state) (c.head (B.select c.state)))

def advance (word : BitString) (c : BankConfiguration Q S k)
    (next : Q) (write : S) (work input : Move) : BankConfiguration Q S k :=
  ⟨next, input.onInput word.length c.inputHead,
    Function.update c.head (B.select c.state) (work.onInt (c.head (B.select c.state))),
    Function.update c.tape (B.select c.state)
      (Function.update (c.tape (B.select c.state)) (c.head (B.select c.state)) write)⟩

/-- Exact instruction count, including zero-step terminal observations. -/
inductive Executes (word : BitString) : BankConfiguration Q S k → ℕ → Bool → Prop
  | accept (c) (table : B.instruction word c = .accept) : Executes word c 0 true
  | reject (c) (table : B.instruction word c = .reject) : Executes word c 0 false
  | step (c) (next write work input) (t result)
      (table : B.instruction word c = .step next write work input)
      (rest : Executes word (B.advance word c next write work input) t result) :
      Executes word c (t + 1) result

def Bounded (_ : TapeBank Q S k) (word : BitString) (r : ℕ) (c : BankConfiguration Q S k) : Prop :=
  c.inputHead ≤ word.length ∧ ∀ j, (c.head j).natAbs ≤ r

theorem initial_bounded (word : BitString) : B.Bounded word 0 B.initialConfiguration := by
  simp [Bounded, initialConfiguration]

theorem advance_bounded (word : BitString) (r : ℕ) (c : BankConfiguration Q S k)
    (next write work input) (h : B.Bounded word r c) :
    B.Bounded word (r + 1) (B.advance word c next write work input) := by
  refine ⟨input.onInput_le _ _ h.1, ?_⟩
  intro j
  by_cases same : j = B.select c.state
  · subst j
    simp only [advance, Function.update_self]
    have bound := h.2 (B.select c.state)
    cases work with
    | stay => exact bound.trans (Nat.le_succ r)
    | left => exact (Int.natAbs_sub_le _ 1).trans (by simpa using Nat.add_le_add_right bound 1)
    | right => exact (Int.natAbs_add_le _ 1).trans (by simpa using Nat.add_le_add_right bound 1)
  · simpa [advance, Function.update_of_ne same] using (h.2 j).trans (Nat.le_succ r)

end TapeBank

end ComplexityOfGenerators.Simulation
