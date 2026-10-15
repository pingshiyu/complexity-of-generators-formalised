import ComplexityOfGenerators.Simulation.SavitchMachine.PairQueries
import ComplexityOfGenerators.Simulation.SavitchMachine.ConfigurationEdge

/-! Compile the fieldwise characterization of a configuration edge. The
finite cases are equality and the two random choices, for each possible native
observation. The resulting query restores both endpoints and the input. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.EdgeQueries

open BooleanTest ConfigurationObservation ConfigurationEdge PairQueries
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {α A O : Type} [DecidableEq α] (M : Machine α A O) (space : PolynomialBound)

theorem target_realizable (old : Option (Fin M.symbols)) (action : Update M) :
    Realizable (radius (M := M) (space := space)) memory (fun x =>
      targetTest M x.source.word (space x.source.word.length) old action x.source.bits x.target) :=
  (((((lift_target (ObservationQueries.state_realizable M space action.state)).and
    (lift_target (ObservationQueries.auxiliary_realizable M space))).and
    (head_realizable M space .input action.input true)).and
    (head_realizable M space .index action.index true)).and
    (head_realizable M space .work action.work false)).and
    (work_realizable M space old action.write)

/-- The complete reachability-leaf query has finite control, rejects malformed
encodings, preserves both endpoint columns, and empties every helper register. -/
theorem reach_realizable [Fintype α] :
    Realizable (radius (M := M) (space := space)) memory (fun x =>
      M.spaceReachBase ⟨x.source.word, [], x.source.word.length⟩ (space x.source.word.length) x.source.bits x.target) := by
  classical
  let predicate (c : Observation M × Option Bool) (x : Context M space) :=
    test M x.source.word (space x.source.word.length) c.1 x.source.bits &&
      (candidate M c.1 c.2).any (fun action =>
        targetTest M x.source.word (space x.source.word.length) c.1.work action x.source.bits x.target)
  have casesRealizable (c : Observation M × Option Bool) : Realizable radius memory (predicate c) := by
    apply (lift_source (ObservationQueries.observation_realizable M space c.1)).and
    cases chosen : candidate M c.1 c.2 with
    | none =>
        simp only [chosen, Option.any_none]
        exact ⟨constant false, constant_correct _ _ _ PairQueries.memory_bound⟩
    | some action =>
        simp only [chosen, Option.any_some]
        exact target_realizable M space c.1.work action
  have allCases := Realizable.exists (PairQueries.memory_bound (M := M) (space := space)) predicate casesRealizable
  have eq : (fun x : Context M space => decide (∃ c, predicate c x = true)) =
      (fun x => M.spaceReachBase ⟨x.source.word, [], x.source.word.length⟩
        (space x.source.word.length) x.source.bits x.target) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Prod.exists, predicate, Bool.and_eq_true]
    exact (reach_iff M x.source.word (space x.source.word.length) x.source.bits x.target).symm
  exact eq ▸ allCases

end
end ComplexityOfGenerators.Simulation.SavitchMachine.EdgeQueries
