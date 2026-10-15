import ComplexityOfGenerators.Simulation.TransducerBank.Space

/-!
# Polynomial-space decision by finite tape-bank programs

The compiler is the existing finite-control, single-work-tape construction.
Its space bound is now operational, independent of its time overhead. Applying
this result requires an actual finite program, termination, and a proved bound
on all its reachable virtual heads.
-/

namespace ComplexityOfGenerators.Simulation.TransducerBank

namespace TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

def Deterministic : Prop := ∀ q input auxiliary index origin symbol,
  match B.transition q input auxiliary index origin symbol with
  | .readRandom _ _ => False
  | _ => True

theorem Executes.change_bits (deterministic : B.Deterministic)
    {data : InputData I A} {bits : BitString} {c : BankConfiguration O Q S k}
    {t : ℕ} {result : Outcome O} (exec : B.Executes data bits c t result) (other : BitString) :
    B.Executes data other c t result := by
  induction exec with
  | accept c table => exact .accept c table
  | reject c table => exact .reject c table
  | exhausted c no yes table absent =>
      have never := deterministic c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some () else none)
        (decide (c.head (B.select c.state) = 0)) (c.tape (B.select c.state) (c.head (B.select c.state)))
      change match B.instruction data c with | .readRandom _ _ => False | _ => True at never
      simp [table] at never
  | random c no yes bit t result table lookup rest ih =>
      have never := deterministic c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some () else none)
        (decide (c.head (B.select c.state) = 0)) (c.tape (B.select c.state) (c.head (B.select c.state)))
      change match B.instruction data c with | .readRandom _ _ => False | _ => True at never
      simp [table] at never
  | step c next write work input auxiliary index emit t result table rest ih =>
      exact .step c next write work input auxiliary index emit t result table ih

end TapeBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S]

theorem bankMachine_deterministic (B : TapeBank I A O Q S k) (h : B.Deterministic) :
    (bankMachine B).Deterministic := by
  intro q input auxiliary index raw
  dsimp only [bankMachine]
  cases phase : (bankControl (Q := Q) (k := k)).symm q with
  | boot => trivial
  | place q negative j => trivial
  | back q negative side => cases h : (bankRead B raw).origin <;> simp [bankTransition, h]
  | seek q negative =>
      cases marked : (bankRead B raw).marked (B.select q)
      · simp [bankTransition, marked]
      · have deterministic := h q input auxiliary index (bankRead B raw).origin
          ((bankRead B raw).symbol (B.select q))
        cases action : B.transition q input auxiliary index (bankRead B raw).origin
            ((bankRead B raw).symbol (B.select q)) <;>
          simp_all [bankTransition]

end
end ComplexityOfGenerators.Simulation.TransducerBank

namespace ComplexityOfGenerators

open Simulation.TransducerBank

noncomputable section

variable {α Q S : Type} {k : ℕ} [Fintype α] [Fintype Q] [Fintype S]

/-- A finite tape-bank decider with polynomial head radius gives a native
polynomial-space decider. Its running time may be arbitrarily large. -/
theorem mem_pspace_of_tapeBank (B : TapeBank α Bool Unit Q S k) (L : Language α)
    (radius : PolynomialBound) (deterministic : B.Deterministic)
    (space : ∀ word, B.SpaceBound (decisionData word) (radius word.length))
    (terminates : ∀ word, ∃ t, ∃ answer : Bool,
      B.Executes (decisionData word) [] B.initialConfiguration t
        (if answer then .accepted [] else .rejected) ∧ (answer = true ↔ word ∈ L)) :
    L ∈ PSPACE α := by
  let p := PolynomialBound.ofPolynomial (2 * radius.asPolynomial + 1)
  have runs (word : List α) (bits : BitString) :
      ∃ t, ∃ answer : Bool, (bankMachine B).run (decisionData word) bits t =
        .halted (if answer then .accepted [] else .rejected) ∧ (answer = true ↔ word ∈ L) := by
    obtain ⟨t, answer, exec, correct⟩ := terminates word
    obtain ⟨ticks, _, run⟩ := bank_run B (decisionData word) bits t _
      (exec.change_bits B deterministic bits)
    exact ⟨ticks, answer, run, correct⟩
  refine ⟨bankMachine B, p, bankMachine_deterministic B deterministic, ?_, ?_, ?_⟩
  · intro word
    obtain ⟨ticks, answer, run, _⟩ := runs word []
    exact ⟨ticks, _, run⟩
  · intro word
    apply Machine.SpaceBound.mono (bankMachine B)
      (bankMachine_spaceBound B (decisionData word) (radius word.length) (space word) ?_)
    · have bound := PolynomialBound.eval_le_ofPolynomial (2 * radius.asPolynomial + 1) word.length
      simpa using bound
    · intro bits
      obtain ⟨t, answer, exec, _⟩ := terminates word
      exact ⟨t, _, exec.change_bits B deterministic bits⟩
  · intro word
    obtain ⟨ticks, answer, run, correct⟩ := runs word []
    constructor
    · rintro ⟨output, t, accepted⟩
      have same := (bankMachine B).halted_outcome_unique _ _ _ _ _ _ accepted run
      cases answer <;> simp_all
    · intro member
      have yes := correct.mpr member
      exact ⟨[], ticks, by simpa [yes] using run⟩

end
end ComplexityOfGenerators
