import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Finite

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

structure FiniteLoopPost (before after : Memory (Cell (β := β) P) α 80) (parts : List ℕ) : Prop where
  origin : after.indexHead = before.indexHead
  output : after.output = []
  path : after.store 31 = []
  factors : ∃ factors : List (List α), List.Forall₂ (fun j word => word ∈ P.layer j) parts factors ∧
    (after.store 70).filterMap (outputLetter P) = factors.flatten.reverse ++ (before.store 70).filterMap (outputLetter P)
  master : after.store 22 = before.store 22

def FiniteLoopResult (before : Memory (Cell (β := β) P) α 80) (parts : List ℕ) : Result (Cell (β := β) P) α 80 → Prop
  | .exhausted => True
  | .done after => FiniteLoopPost P before after parts

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

include retract in
theorem loop_runs_total (inputIndex : ℕ) (parts : List ℕ) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode parts) (indices : ∀ j ∈ parts, j ≤ inputIndex) :
    ∃ ticks result, (loop P decode).Runs inputIndex bits m ticks result ∧ FiniteLoopResult P m parts result := by
  induction parts generalizing m with
  | nil =>
      have wordEmpty : m.store 31 = [] := by simpa [pathWord, StarPaths.payload] using path
      refine ⟨0, .done m, Command.Runs.loop_stop m 31 _ _ (by simp [observe, wordEmpty]), ?_⟩
      exact ⟨rfl, empty, wordEmpty, ⟨[], .nil, by simp⟩, rfl⟩
  | cons j parts ih =>
      obtain ⟨first, result, firstRun, firstPost⟩ := call_runs_total P encode decode retract inputIndex j parts bits m
        origin empty path (indices j (by simp))
      cases result with
      | exhausted =>
          exact ⟨1+first, .exhausted, Command.Runs.loop_absent m 31 _ _ first
            (by simp [observe, path, pathWord_cons]) firstRun, trivial⟩
      | done after =>
          obtain ⟨failures, word, post, member⟩ := firstPost
          obtain ⟨rest, result, restRun, restPost⟩ := ih after (post.origin.trans origin) post.output post.path
            (fun k belongs => indices k (by simp [belongs]))
          refine ⟨1+first+1+rest, result, Command.Runs.loop m after 31 _ _ first rest result
            (by simp [observe, path, pathWord_cons]) firstRun restRun, ?_⟩
          cases result with
          | exhausted => trivial
          | done next =>
              constructor
              · exact restPost.origin.trans post.origin
              · exact restPost.output
              · exact restPost.path
              · obtain ⟨factors, language, output⟩ := restPost.factors
                refine ⟨word::factors, .cons member language, ?_⟩
                rw [output, post.buffer]
                simp [List.reverse_append, List.append_assoc]
              · exact restPost.master.trans (post.frame 22 (outside_inner 22 (Or.inl (by decide)))
                  (by decide) (by decide) (by decide) (by decide))

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
