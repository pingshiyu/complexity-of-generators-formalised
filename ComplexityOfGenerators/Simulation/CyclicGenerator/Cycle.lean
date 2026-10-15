import ComplexityOfGenerators.Simulation.CyclicGenerator.RoutineSpace

/-! Termination of cyclic enumeration on every finite random tape. A pass
which found an accepted word may restart, but doing so clears its `seen` flag.
Declining a word consumes a random bit. These events, together with the strictly
increasing word rank within a pass, give a well-founded execution measure. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

def cycleBudget (bits : BitString) (seen : Bool) (random : ℕ) : ℕ :=
  2 * (bits.length - random) + if seen then 1 else 0

def cyclePotential (bits : BitString) (n : ℕ) (word : List α) (seen : Bool) (random : ℕ) : ℕ :=
  cycleBudget bits seen random * (Fintype.card α ^ n + 1) + (Fintype.card α ^ n - wordRank word)

theorem lexPotential {N a b x y : ℕ} (xBound : x ≤ N) (yBound : y ≤ N)
    (order : a < b ∨ a = b ∧ x < y) : a * (N + 1) + x < b * (N + 1) + y := by
  rcases order with less | ⟨rfl, less⟩ <;> nlinarith

def AllowedOutcome (D : Machine α Bool Unit) (n : ℕ) : Outcome α → Prop
  | .accepted word => word.length = n ∧ D.Accepts (decisionData word) []
  | .exhausted => True
  | .rejected => False

variable (D : Machine α Bool Unit)

theorem cycle_terminates (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (bits : BitString) (word : List α) (seen : Bool) (random position : ℕ)
    (length : word.length = n) (positionBound : position ≤ n) :
    ∃ result, (bank D).RegionRun (generatorData n) bits (radius n s)
      (candidateConfig D word seen random position) result ∧ AllowedOutcome D n result := by
  generalize measure_eq : cyclePotential bits n word seen random = measure
  induction measure using Nat.strong_induction_on generalizing word seen random position with
  | h measure ih =>
      have proceed (afterSeen : Bool) (afterRandom : ℕ)
          (progress : cycleBudget bits afterSeen afterRandom ≤ cycleBudget bits seen random) :
          ∃ result, (bank D).RegionRun (generatorData n) bits (radius n s)
            {candidateConfig D word afterSeen afterRandom 0 with state := .increment afterSeen} result ∧
            AllowedOutcome D n result := by
        let next := incrementWord first word
        have nextLength : next.word.length = n := (incrementWord_length first word).trans length
        have nextPosition : next.position ≤ n := by
          have := incrementWord_cost first word
          dsimp [next]
          omega
        have counter := increment_inRegion D first least word afterSeen afterRandom s bits
        rw [length] at counter
        have rank := incrementWord_rank first least word
        cases overflow : next.overflow with
        | false =>
            have overflow' : (incrementWord first word).overflow = false := overflow
            have increasing : wordRank next.word = wordRank word + 1 := by
              simpa only [overflow', Bool.false_eq_true,
                if_false] using rank
            have less : cyclePotential bits n next.word afterSeen afterRandom < measure := by
              rw [← measure_eq]
              apply lexPotential (Nat.sub_le _ _) (Nat.sub_le _ _)
              rcases lt_or_eq_of_le progress with strict | equal
              · exact Or.inl strict
              · right
                refine ⟨equal, ?_⟩
                have bound := wordRank_lt word
                rw [length] at bound
                omega
            obtain ⟨result, run, allowed⟩ := ih _ less next.word afterSeen afterRandom next.position
              nextLength nextPosition rfl
            refine ⟨result, run.prepend (bank D) (t := next.position + 1) ?_, allowed⟩
            simpa only [overflow', Bool.false_eq_true,
              if_false, candidateConfig, next] using counter
        | true =>
            have overflow' : (incrementWord first word).overflow = true := overflow
            have last : next.position = n := by
              have info : wordRank word + 1 = Fintype.card α ^ word.length ∧
                  next.word = List.replicate word.length first ∧ next.position = word.length := by
                simpa only [overflow', if_true] using rank
              exact info.2.2.trans length
            have last' : (incrementWord first word).position = n := last
            have counter' : (bank D).RegionSteps (generatorData n) bits (radius n s)
                {candidateConfig D word afterSeen afterRandom 0 with state := .increment afterSeen}
                n {candidateConfig D next.word afterSeen afterRandom n with state := .increment afterSeen} := by
              simpa only [overflow', if_true,
                Nat.add_zero, last'] using counter
            cases afterSeen with
            | false =>
                have run := empty_pass_inRegion D next.word afterRandom s bits
                rw [nextLength] at run
                exact ⟨.exhausted, run.prepend (bank D) counter', trivial⟩
            | true =>
                have less : cyclePotential bits n next.word false afterRandom < measure := by
                  rw [← measure_eq]
                  apply lexPotential (Nat.sub_le _ _) (Nat.sub_le _ _)
                  left
                  simp only [cycleBudget, if_true, Bool.false_eq_true, if_false] at progress ⊢
                  omega
                obtain ⟨result, run, allowed⟩ := ih _ less next.word false afterRandom n nextLength le_rfl rfl
                have restart := (overflow_restart D next.word afterRandom bits).inRegion (bank D) next.word.length
                  ((candidate_bounded D next.word true afterRandom next.word.length le_rfl).with_state (bank D) _)
                rw [nextLength] at restart
                have restart' := restart.mono (bank D) (show n + 1 ≤ radius n s by unfold radius; omega)
                exact ⟨result, (run.prepend (bank D) restart').prepend (bank D) counter', allowed⟩
      obtain ⟨ticks, terminal, test, geometry, visited, input, action, answer⟩ :=
        candidate_decision D deterministic word seen random position s bits
          (by omega) (halts word length) (space word length)
      rw [length] at test
      have work : terminal.workHead.natAbs ≤ s := by have := geometry.workHead_bound D; omega
      rcases action with accepts | rejects
      · cases coin : bits[random]? with
        | none =>
            have bound := (decisionConfig_bounded D word seen random s terminal input work).mono (bank D)
              (show word.length + s ≤ radius word.length s by unfold radius; omega)
            have run : (bank D).RegionRun (generatorData word.length) bits (radius word.length s)
                (decisionConfig D word seen random terminal) .exhausted :=
              ⟨0, _, .refl _ bound, selection_exhausted D word seen random bits terminal accepts coin⟩
            rw [length] at run
            exact ⟨.exhausted, run.prepend (bank D) test, trivial⟩
        | some bit =>
            cases bit with
            | false =>
                have run := select_word_inRegion D word seen random s bits terminal input work accepts coin
                rw [length] at run
                exact ⟨.accepted word, run.prepend (bank D) test, length, answer.mp accepts⟩
            | true =>
                have randomBound := (List.getElem?_eq_some_iff.mp coin).1
                have progress : cycleBudget bits true (random + 1) ≤ cycleBudget bits seen random := by
                  cases seen <;> simp only [cycleBudget, if_true, Bool.false_eq_true, if_false] <;> omega
                obtain ⟨result, run, allowed⟩ := proceed true (random + 1) progress
                obtain ⟨cleanupTicks, cleanup⟩ := restart_inRegion D word true (random + 1) s bits terminal
                  geometry input visited
                have decline := decline_word_inRegion D word seen random s bits terminal input work accepts coin
                rw [length] at cleanup decline
                exact ⟨result, ((run.prepend (bank D) cleanup).prepend (bank D) decline).prepend (bank D) test, allowed⟩
      · obtain ⟨result, run, allowed⟩ := proceed seen random le_rfl
        obtain ⟨cleanupTicks, cleanup⟩ := restart_inRegion D word seen random s bits terminal geometry input visited
        have reject := reject_word_inRegion D word seen random s bits terminal input work rejects
        rw [length] at cleanup reject
        exact ⟨result, ((run.prepend (bank D) cleanup).prepend (bank D) reject).prepend (bank D) test, allowed⟩

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
