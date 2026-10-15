import ComplexityOfGenerators.Simulation.OutputMatcher
import ComplexityOfGenerators.Foundations.SpaceReachability
import ComplexityOfGenerators.Proofs.GeneratorSupport

/-!
# Output comparison preserves work space

The existing streaming comparator keeps only a mismatch flag in finite control
and uses the ordinary input head as its output position. It copies the source
work tape and visited-cell history exactly, including the terminal successor.
Thus a space-bounded generator reduces to finite configuration reachability
without storing its potentially unbounded output history.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

/-- Streaming comparison preserves the exact visited-cell bound. -/
theorem outputMatcher_spaceBound (data : InputData α Bool) (s : ℕ)
    (space : M.SpaceBound (matcherSourceData data) s) :
    (outputMatcher M).SpaceBound data s := by
  refine ⟨space.1, ?_⟩
  intro bits t current running
  rw [outputMatcher_run M data bits t] at running
  cases source : M.run (matcherSourceData data) bits t with
  | halted result => simp [source, matcherResult] at running
  | running c =>
      simp only [source, matcherResult, RunState.running.injEq] at running
      subst current
      refine ⟨(space.2 bits t c source).1, ?_⟩
      intro next step
      rw [outputMatcher_next] at step
      cases successor : M.next (matcherSourceData data) bits c with
      | halted result => simp [successor, matcherResult] at step
      | running d =>
          simp only [successor, matcherResult, RunState.running.injEq] at step
          subst next
          exact (space.2 bits t c source).2 d successor

/-- Acceptance by the streaming comparator is exactly production of the input
word, on the same random tape and with the same supplied family index. -/
theorem outputMatcher_accepts_iff (data : InputData α Bool) (bits : BitString) :
    (outputMatcher M).Accepts data bits ↔ M.Produces (matcherSourceData data) bits data.input := by
  constructor
  · rintro ⟨out, t, accepted⟩
    rw [outputMatcher_run] at accepted
    cases source : M.run (matcherSourceData data) bits t with
    | running c => simp [source, matcherResult] at accepted
    | halted result =>
        cases result with
        | exhausted => simp [source, matcherResult, matcherOutcome] at accepted
        | rejected => simp [source, matcherResult, matcherOutcome] at accepted
        | accepted word =>
            by_cases same : word = data.input
            · exact ⟨t, same ▸ source⟩
            · simp [source, matcherResult, matcherOutcome, same] at accepted
  · rintro ⟨t, produced⟩
    refine ⟨[], t, ?_⟩
    rw [outputMatcher_run, produced]
    simp [matcherResult, matcherOutcome]

/-- The finite graph uses the queried word as ordinary input and its length as
the unary index. Turning this graph algorithm into a native decider still
requires a space-bounded implementation of reachability. -/
theorem generatedWord_iff_boundedDecisionPath (word : List α) (s : ℕ)
    (space : M.SpaceBound (generatorData word.length) s) :
    word ∈ M.generatedLanguage (generatorData word.length) ↔
      ∃ finish : (outputMatcher M).BoundedDecisionView ⟨word, [], word.length⟩ s,
        Relation.ReflTransGen ((outputMatcher M).BoundedDecisionEdge ⟨word, [], word.length⟩ s)
          ((outputMatcher M).boundedInitialView ⟨word, [], word.length⟩ s) finish ∧
        finish.val.Accepting (outputMatcher M) ⟨word, [], word.length⟩ := by
  let data : InputData α Bool := ⟨word, [], word.length⟩
  have bounded : (outputMatcher M).SpaceBound data s := outputMatcher_spaceBound M data s space
  rw [← bounded.accepts_iff_boundedDecisionPath (outputMatcher M)]
  simp only [outputMatcher_accepts_iff]
  constructor
  · rintro ⟨bits, _, produced⟩
    exact ⟨bits, produced⟩
  · rintro ⟨bits, produced⟩
    exact ⟨bits ++ [false], by simp, M.produces_append _ bits [false] word produced⟩

end
end ComplexityOfGenerators.Simulation
