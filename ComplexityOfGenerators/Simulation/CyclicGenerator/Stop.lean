import ComplexityOfGenerators.Simulation.CyclicGenerator.Cycle

/-! For a nonempty length slice, a stop bit eventually selects a word. The
`Before` invariant records why an empty-pass exit is impossible: if no accepted
candidate has been seen, every earlier candidate was rejected. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

def Before (D : Machine α Bool Unit) (n : ℕ) (word : List α) (seen : Bool) : Prop :=
  seen = false → ∀ v : List α, v.length = n → wordRank v < wordRank word → ¬D.Accepts (decisionData v) []

variable (D : Machine α Bool Unit)

theorem cycle_accepts_stop (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (nonempty : ∃ v : List α, v.length = n ∧ D.Accepts (decisionData v) [])
    (bits : BitString) (word : List α) (seen : Bool) (random position : ℕ)
    (length : word.length = n) (positionBound : position ≤ n)
    (before : Before D n word seen) (stop : false ∈ bits.drop random) :
    ∃ output, (bank D).RegionRun (generatorData n) bits (radius n s)
      (candidateConfig D word seen random position) (.accepted output) := by
  generalize measure_eq : cyclePotential bits n word seen random = measure
  induction measure using Nat.strong_induction_on generalizing word seen random position with
  | h measure ih =>
      have proceed (afterSeen : Bool) (afterRandom : ℕ)
          (progress : cycleBudget bits afterSeen afterRandom ≤ cycleBudget bits seen random)
          (earlier : afterSeen = false → ∀ v : List α, v.length = n → wordRank v ≤ wordRank word →
            ¬D.Accepts (decisionData v) []) (stops : false ∈ bits.drop afterRandom) :
          ∃ output, (bank D).RegionRun (generatorData n) bits (radius n s)
            {candidateConfig D word afterSeen afterRandom 0 with state := .increment afterSeen} (.accepted output) := by
        let next := incrementWord first word
        have nextLength : next.word.length = n := (incrementWord_length first word).trans length
        have nextPosition : next.position ≤ n := by have := incrementWord_cost first word; dsimp [next]; omega
        have counter := increment_inRegion D first least word afterSeen afterRandom s bits
        rw [length] at counter
        have rank := incrementWord_rank first least word
        cases overflow : next.overflow with
        | false =>
            have overflow' : (incrementWord first word).overflow = false := overflow
            have increasing : wordRank next.word = wordRank word + 1 := by simpa only [overflow',
              Bool.false_eq_true, ite_false] using rank
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
            have beforeNext : Before D n next.word afterSeen := by
              intro unseen v vLength rankBound
              exact earlier unseen v vLength (by omega)
            obtain ⟨output, run⟩ := ih _ less next.word afterSeen afterRandom next.position
              nextLength nextPosition beforeNext stops rfl
            refine ⟨output, run.prepend (bank D) (t := next.position + 1) ?_⟩
            simpa only [overflow', Bool.false_eq_true, ite_false, candidateConfig, next] using counter
        | true =>
            have overflow' : (incrementWord first word).overflow = true := overflow
            have info : wordRank word + 1 = Fintype.card α ^ word.length ∧
                next.word = List.replicate word.length first ∧ next.position = word.length := by
              simpa only [overflow', ite_true] using rank
            have last : (incrementWord first word).position = n := info.2.2.trans length
            have counter' : (bank D).RegionSteps (generatorData n) bits (radius n s)
                {candidateConfig D word afterSeen afterRandom 0 with state := .increment afterSeen}
                n {candidateConfig D next.word afterSeen afterRandom n with state := .increment afterSeen} := by
              simpa only [overflow', ite_true, Nat.add_zero, last] using counter
            cases afterSeen with
            | false =>
                obtain ⟨v, vLength, accepted⟩ := nonempty
                have bound := wordRank_lt v
                have lastRank := info.1
                rw [length] at lastRank
                rw [vLength] at bound
                exact False.elim (earlier rfl v vLength (by omega) accepted)
            | true =>
                have less : cyclePotential bits n next.word false afterRandom < measure := by
                  rw [← measure_eq]
                  apply lexPotential (Nat.sub_le _ _) (Nat.sub_le _ _)
                  left
                  simp only [cycleBudget, ite_true, Bool.false_eq_true, ite_false] at progress ⊢
                  omega
                have beforeNext : Before D n next.word false := by
                  intro _ v _ rankBound
                  rw [info.2.1, wordRank_replicate first least] at rankBound
                  omega
                obtain ⟨output, run⟩ := ih _ less next.word false afterRandom n nextLength le_rfl beforeNext stops rfl
                have restart := (overflow_restart D next.word afterRandom bits).inRegion (bank D) next.word.length
                  ((candidate_bounded D next.word true afterRandom next.word.length le_rfl).with_state (bank D) _)
                rw [nextLength] at restart
                have restart' := restart.mono (bank D) (show n + 1 ≤ radius n s by unfold radius; omega)
                exact ⟨output, (run.prepend (bank D) restart').prepend (bank D) counter'⟩
      obtain ⟨ticks, terminal, test, geometry, visited, input, action, answer⟩ :=
        candidate_decision D deterministic word seen random position s bits
          (by omega) (halts word length) (space word length)
      rw [length] at test
      have work : terminal.workHead.natAbs ≤ s := by have := geometry.workHead_bound D; omega
      rcases action with accepts | rejects
      · cases coin : bits[random]? with
        | none =>
            have outside := List.getElem?_eq_none_iff.mp coin
            rw [List.drop_eq_nil_iff.mpr outside] at stop
            simp at stop
        | some bit =>
            cases bit with
            | false =>
                have run := select_word_inRegion D word seen random s bits terminal input work accepts coin
                rw [length] at run
                exact ⟨word, run.prepend (bank D) test⟩
            | true =>
                obtain ⟨randomBound, lookup⟩ := List.getElem?_eq_some_iff.mp coin
                have progress : cycleBudget bits true (random + 1) ≤ cycleBudget bits seen random := by
                  cases seen <;> simp only [cycleBudget, ite_true, Bool.false_eq_true, ite_false] <;> omega
                have stops : false ∈ bits.drop (random + 1) := by
                  rw [List.drop_eq_getElem_cons randomBound, lookup] at stop
                  simpa using stop
                obtain ⟨output, run⟩ := proceed true (random + 1) progress (by intro impossible; cases impossible) stops
                obtain ⟨cleanupTicks, cleanup⟩ := restart_inRegion D word true (random + 1) s bits terminal
                  geometry input visited
                have decline := decline_word_inRegion D word seen random s bits terminal input work accepts coin
                rw [length] at cleanup decline
                exact ⟨output, ((run.prepend (bank D) cleanup).prepend (bank D) decline).prepend (bank D) test⟩
      · have rejected : ¬D.Accepts (decisionData word) [] := by
          intro accepted
          have impossible := answer.mpr accepted
          rw [rejects] at impossible
          cases impossible
        have earlier : seen = false → ∀ v : List α, v.length = n → wordRank v ≤ wordRank word →
            ¬D.Accepts (decisionData v) [] := by
          intro unseen v vLength rankBound
          rcases lt_or_eq_of_le rankBound with strict | same
          · exact before unseen v vLength strict
          · have equal := wordRank_injective_of_length (vLength.trans length.symm) same
            simpa [equal] using rejected
        obtain ⟨output, run⟩ := proceed seen random le_rfl earlier stop
        obtain ⟨cleanupTicks, cleanup⟩ := restart_inRegion D word seen random s bits terminal geometry input visited
        have reject := reject_word_inRegion D word seen random s bits terminal input work rejects
        rw [length] at cleanup reject
        exact ⟨output, ((run.prepend (bank D) cleanup).prepend (bank D) reject).prepend (bank D) test⟩

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
