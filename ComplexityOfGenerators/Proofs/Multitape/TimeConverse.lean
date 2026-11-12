import ComplexityOfGenerators.Proofs.Multitape.UpToFamily
import ComplexityOfGenerators.Proofs.Multitape.MonotoneEnvelopes
import ComplexityOfGenerators.Proofs.Multitape.UpToResourceBounds
import ComplexityOfGenerators.Proofs.Multitape.UpToElementary
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Bounds
import ComplexityOfGenerators.Proofs.Multitape.TimeContainment

/-! The converse uses one real finite bank: guess a bounded word, simulate the
source nondeterministic decider, and replay the word or a fixed shortest fallback.
The source already bounds every branch, so no additional clock is assumed.
Monotonicity bounds the resources of every shorter proposed word by O(t(n)). -/

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Simulation.TransducerBank.UpToGeneration

variable {α : Type} [Fintype α]

theorem ntime_subset_gtimeUpTo (time : ℕ → ℕ) (monotone : Monotone time)
    (dominates : ∀ n, n ≤ time n) : NTIME α time ⊆ GTIMEUpTo α time := by
  classical
  intro language member
  by_cases nonempty : language.Nonempty
  · obtain ⟨source, runtime, order, bounded, recognizes⟩ := member
    have lengths : ∃ n, ∃ word ∈ language, word.length = n := by
      obtain ⟨word, inLanguage⟩ := nonempty
      exact ⟨word.length, word, inLanguage, rfl⟩
    obtain ⟨fallback, fallbackMember, fallbackLength⟩ := Nat.find_spec lengths
    have shortest : ∀ word ∈ language, fallback.length ≤ word.length := by
      intro word inLanguage
      rw [fallbackLength]
      exact Nat.find_min' lengths ⟨word, inLanguage, rfl⟩
    have termination : ∀ word, ∃ bound, source.TimeBound (decisionData word) bound :=
      fun word => ⟨runtime word.length, bounded word⟩
    obtain ⟨copies, positive, envelope⟩ :=
      monotone_time_envelope source runtime time order monotone bounded
    let family := upToFamily language source fallback termination recognizes fallbackMember shortest
    refine ⟨family, (fun n => trialBudget fallback n (copies * (time n + 1))),
      upToFamily_language language source fallback termination recognizes fallbackMember shortest,
      upTo_timeBudget_order fallback copies time dominates, ?_⟩
    intro n
    change (machine source fallback).AcceptingTimeBound (generatorData n)
      (trialBudget fallback n (copies * (time n + 1)))
    exact machine_acceptingTimeBound source fallback n (copies * (time n + 1)) (envelope n)
  · have empty : language = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    simpa only [empty] using (empty_mem_gtimeUpTo (α := α) time)

/-- The full TIME equality in Proposition 4.2, on the genuine fixed-bank model. -/
theorem gtimeUpTo_eq_ntime (time : ℕ → ℕ) (constructible : TimeConstructible time)
    (monotone : Monotone time) (dominates : ∀ n, n ≤ time n) : GTIMEUpTo α time = NTIME α time :=
  Set.Subset.antisymm (gtimeUpTo_subset_ntime time constructible dominates)
    (ntime_subset_gtimeUpTo time monotone dominates)

end
end ComplexityOfGenerators.Multitape
