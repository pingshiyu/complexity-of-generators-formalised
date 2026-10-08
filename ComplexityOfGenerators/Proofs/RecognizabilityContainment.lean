import ComplexityOfGenerators.Proofs.RecursiveGenerator
import ComplexityOfGenerators.Proofs.ClockProgram
import ComplexityOfGenerators.Proofs.ElementaryGenerators

/-!
# The recognizer-to-generator half of Theorem 3.1

For a nonempty recognized language, fix a member as fallback. Sample a candidate
word code and a finite simulation clock; return the candidate if the recognizer
accepts within that clock, and the fallback otherwise. The native construction
implements this total algorithm with finite control and accepts almost surely.
The empty language uses the separate tape-exhausting generator.
-/

namespace ComplexityOfGenerators

open Simulation Encodable

/-- Completed containment in Theorem 3.1. The constructed generator uses the
original machine model and has exactly the original word language. No resource
bound or decidability assumption is imposed on the recognizer. -/
theorem re_subset_gen (α : Type) [Fintype α] : RE α ⊆ GEN α := by
  classical
  let : Primcodable α := Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)
  intro L recognized
  by_cases nonempty : L.Nonempty
  · obtain ⟨fallback, fallbackMember⟩ := nonempty
    obtain ⟨M, deterministic, recognizes⟩ := recognized
    let code := clockedWordCode M fallback
    let f := clockedCandidate M fallback
    have computes := clockedWordCode_eval M fallback
    refine ⟨recursiveGenerator code, recursiveGenerator_isGenerator code f computes (generatorData 0), ?_⟩
    rw [recursiveGenerator_language code f computes]
    ext word
    constructor
    · rintro ⟨clock, candidate, rfl⟩
      exact clockedCandidate_sound M fallback fallbackMember recognizes clock candidate
    · intro member
      obtain ⟨output, clock, run⟩ := (recognizes word).mpr member
      have test : acceptingResult M (finiteRun M (decisionData word) [] clock) = true :=
        (acceptingResult_correct M _).mpr
          ⟨output, (finiteRun_accepts_iff M (decisionData word) [] clock output).mpr run⟩
      exact ⟨clock, encode word, by simp [f, clockedCandidate, test]⟩
  · have empty : L = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    rw [empty]
    exact empty_language_in_gen

end ComplexityOfGenerators
