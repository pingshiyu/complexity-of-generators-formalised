import ComplexityOfGenerators.Simulation.DecisionChoice
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds
import ComplexityOfGenerators.Simulation.ClockArithmetic

/-! Binary union closure of the retained native NP class, using an actual
one-bit branch choice and the verified finite-bank compiler. -/

namespace ComplexityOfGenerators

open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

def decisionChoice (M : Bool → Machine α Bool Unit) : Machine α Bool Unit :=
  TransducerBank.bankMachine (choiceBank M)

theorem decisionChoice_branch (M : Bool → Machine α Bool Unit) (b : Bool) (word : List α) (bits : BitString)
    (t : ℕ) (result : Outcome Unit) (source : (M b).run (decisionData word) bits t = .halted result) :
    ∃ ticks, ticks ≤ 1 + (t + 2) * (2 * (t + 1) + 4) ∧
      (decisionChoice M).run (decisionData word) (b :: bits) ticks = .halted (choiceOutcome result) := by
  obtain ⟨ticks, bound, branch⟩ := choice_executes M b word bits (M b).initialConfiguration t result
    (by simpa only [Machine.runFrom_initial] using source)
  have start : (choiceBank M).Executes (decisionData word) (b :: bits) (choiceBank M).initialConfiguration (ticks + 1) (choiceOutcome result) := by
    apply TransducerBank.TapeBank.Executes.random _ (some ⟨false, (M false).initial⟩) (some ⟨true, (M true).initial⟩) b ticks _ rfl rfl
    cases b <;>
      simpa [TransducerBank.TapeBank.choose, TransducerBank.TapeBank.initialConfiguration,
        choiceBank, choiceConfiguration, Machine.initialConfiguration] using branch
  obtain ⟨nativeTicks, cost, native⟩ := TransducerBank.bank_run (choiceBank M) (decisionData word) (b :: bits) _ _ start
  refine ⟨nativeTicks, cost.trans ?_, native⟩
  nlinarith

def decisionChoiceTime (p q : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (1 + ((p.add q).asPolynomial + 2) * (2 * ((p.add q).asPolynomial + 1) + 4))

theorem decisionChoiceTime_bound (p q : PolynomialBound) (n t : ℕ) (bound : t ≤ p.add q n) :
    1 + (t + 2) * (2 * (t + 1) + 4) ≤ decisionChoiceTime p q n := by
  have poly := PolynomialBound.eval_le_ofPolynomial
    (1 + ((p.add q).asPolynomial + 2) * (2 * ((p.add q).asPolynomial + 1) + 4)) n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
    PolynomialBound.asPolynomial_eval] at poly
  change _ ≤ PolynomialBound.ofPolynomial _ n
  apply le_trans _ poly
  nlinarith

theorem np_union {L K : Language α} (left : L ∈ NP α) (right : K ∈ NP α) : L ∪ K ∈ NP α := by
  obtain ⟨M₀, p, bound₀, language₀⟩ := left
  obtain ⟨M₁, q, bound₁, language₁⟩ := right
  let M := fun b : Bool => if b then M₁ else M₀
  let time := fun b : Bool => if b then q else p
  have bounded (b : Bool) (word : List α) : (M b).TimeBound (decisionData word) (time b word.length) := by
    cases b with
    | false => exact bound₀ word
    | true => exact bound₁ word
  have smaller (b : Bool) (n : ℕ) : time b n ≤ p.add q n := by
    have sum := p.add_le q n
    cases b <;> dsimp [time] <;> omega
  have nil (word : List α) : ∃ t, t ≤ 5 ∧ (decisionChoice M).run (decisionData word) [] t = .halted .exhausted := by
    have exhausted : (choiceBank M).Executes (decisionData word) [] (choiceBank M).initialConfiguration 0 .exhausted :=
      .exhausted _ _ _ rfl rfl
    simpa only [decisionChoice] using TransducerBank.bank_run (choiceBank M) (decisionData word) [] 0 .exhausted exhausted
  refine ⟨decisionChoice M, decisionChoiceTime p q, ?_, ?_⟩
  · intro word bits
    cases bits with
    | nil =>
        obtain ⟨t, bound, halted⟩ := nil word
        have budget := decisionChoiceTime_bound p q word.length 0 (Nat.zero_le _)
        exact (decisionChoice M).haltsWithin_mono _ [] (by omega) ⟨.exhausted, halted⟩
    | cons b bits =>
        obtain ⟨result, source⟩ := bounded b word bits
        obtain ⟨ticks, cost, native⟩ := decisionChoice_branch M b word bits _ result source
        exact (decisionChoice M).haltsWithin_mono _ _ (cost.trans (decisionChoiceTime_bound p q _ _ (smaller b _))) ⟨_, native⟩
  · intro word
    constructor
    · rintro ⟨bits, out, t, accepted⟩
      cases bits with
      | nil =>
          obtain ⟨s, _, halted⟩ := nil word
          have impossible := (decisionChoice M).halted_outcome_unique _ [] t s _ _ accepted halted
          cases impossible
      | cons b bits =>
          obtain ⟨result, source⟩ := bounded b word bits
          obtain ⟨ticks, _, native⟩ := decisionChoice_branch M b word bits _ result source
          have same := (decisionChoice M).halted_outcome_unique _ _ t ticks _ _ accepted native
          cases result with
          | rejected => cases same
          | exhausted => cases same
          | accepted w =>
              have branch : (M b).Accepts (decisionData word) bits := ⟨w, _, source⟩
              cases b with
              | false => exact Or.inl ((language₀ word).mp ⟨bits, branch⟩)
              | true => exact Or.inr ((language₁ word).mp ⟨bits, branch⟩)
    · intro member
      have branch : ∃ b bits, (M b).Accepts (decisionData word) bits := by
        rcases member with h | h
        · obtain ⟨bits, accepts⟩ := (language₀ word).mpr h
          exact ⟨false, bits, accepts⟩
        · obtain ⟨bits, accepts⟩ := (language₁ word).mpr h
          exact ⟨true, bits, accepts⟩
      obtain ⟨b, bits, out, t, accepted⟩ := branch
      obtain ⟨ticks, _, native⟩ := decisionChoice_branch M b word bits t (.accepted out) accepted
      exact ⟨b :: bits, [], ticks, native⟩

end
end ComplexityOfGenerators
