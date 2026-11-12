import ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns.Reachability

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
open Multitape.SpaceConfigurations
set_option backward.isDefEq.respectTransparency false
variable {I O Q S : Type} {k : ℕ} [Fintype Q] [Fintype S]

theorem short_accepting_run_from (source : TapeBank I Bool O Q S k) (word : List I) (choices : BitString) (radius : ℕ)
    {c : BankConfiguration O Q S k} {ticks : ℕ} {result : List O}
    (run : source.Executes (decisionData word) choices c ticks (.accepted result))
    (valid : Valid source.blank word.length radius (snapshot c))
    (allBound : ∀ time finish, source.Steps (decisionData word) choices c time finish →
      source.Bounded (decisionData word) radius finish) :
    ∃ shortChoices shortTime shortResult,
      shortTime<2^(clockWidth (Q:=Q) (S:=S) (k:=k) word.length radius) ∧
      source.Executes (decisionData word) shortChoices ((snapshot c).restore 0 []) shortTime (.accepted shortResult) := by
  let start : Vertex (Q:=Q) (k:=k) source.blank word.length radius := ⟨snapshot c,valid⟩
  obtain ⟨target,path,terminal⟩ := accepted_reachable source word choices radius run valid allBound
  obtain ⟨tail,chain,small,last⟩ := exists_short_chain path
  have mappedChain : (start.val::tail.map Subtype.val).IsChain (Next source word) := by
    simpa only [List.map_cons] using (List.isChain_map Subtype.val).mpr chain
  have mappedLast : (start.val::tail.map Subtype.val).getLast (by simp)=target.val := by
    change ((start::tail).map Subtype.val).getLast (by simp)=target.val
    rw [List.getLast_map]
    exact congrArg Subtype.val last
  obtain ⟨suffix,output,execution⟩ := replay_chain source word (tail.map Subtype.val) start.val mappedChain
    (by rw [mappedLast];exact terminal) [] []
  exact ⟨suffix,tail.length,output,small.trans_le (vertex_card_le source.blank word.length radius),
    by simpa only [List.length_map,List.nil_append,List.length_nil] using execution⟩

/-- A bounded-space bank never needs an accepting branch as long as its
finite configuration graph. The theorem supplies a real finite choice tape. -/
theorem short_accepting_run (source : TapeBank I Bool O Q S k) (word : List I) (radius : ℕ)
    (space : source.SpaceBound (decisionData word) radius)
    {choices : BitString} {ticks : ℕ} {result : List O}
    (run : source.Executes (decisionData word) choices source.initialConfiguration ticks (.accepted result)) :
    ∃ shortChoices shortTime shortResult,
      shortTime<2^(clockWidth (Q:=Q) (S:=S) (k:=k) word.length radius) ∧
      source.Executes (decisionData word) shortChoices source.initialConfiguration shortTime (.accepted shortResult) := by
  exact short_accepting_run_from source word choices radius run (initial_valid source word.length radius)
    (fun time finish path => space choices time finish path)

end ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
