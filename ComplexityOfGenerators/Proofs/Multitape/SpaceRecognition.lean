import ComplexityOfGenerators.Proofs.Multitape.SpaceClockBounds
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Language

/-! Bound every nondeterministic branch by a genuine space-constructed binary
clock. Language preservation uses an actual short accepting seed; the source
only needs finite-seed termination and its supplied space bound. -/
namespace ComplexityOfGenerators.Multitape
open Simulation.TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {space : ℕ→ℕ}

noncomputable def spaceRecognizer (constructor : SpaceConstructor space)
    (source : MultitapeMachine α Bool Unit) (copies : ℕ) : MultitapeMachine α Bool Unit where
  inputFinite := source.inputFinite
  auxiliaryFinite := source.auxiliaryFinite
  outputFinite := source.outputFinite
  Control := SpaceDecision.Control constructor.machine.Control source.Control copies
  Work := SpaceDecision.Symbol constructor.machine.Work source.Work
  controlFinite := inferInstance
  workFinite := inferInstance
  tapes := source.tapes+(constructor.machine.tapes+2)
  program := SpaceDecision.bank constructor.machine.program source.program copies

theorem ordinary_input_mem_nspace (language : Language α) (source : MultitapeMachine α Bool Unit)
    (workspace space : ℕ→ℕ) (constructible : SpaceConstructible space)
    (order : ResourceOrder workspace space) (logarithm : ResourceOrder (fun n=>Nat.clog 2 (n+1)) space)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n)
    (terminates : ∀ word,source.Terminates (decisionData word))
    (bounded : ∀ word,source.SpaceBound (decisionData word) (workspace word.length))
    (correct : ∀ word,(∃ bits,source.Accepts (decisionData word) bits) ↔ word∈language) :
    language∈NSPACE α space := by
  obtain ⟨constructor⟩ := constructible
  obtain ⟨copies,_,enough⟩ := exists_space_clock_copies constructor source workspace order
  let target := spaceRecognizer constructor source copies
  have radiusMember : language∈RadiusNSPACE α space := by
    refine ⟨target,(fun n=>SpaceDecision.totalRadius constructor copies (workspace n) n),
      totalRadius_resourceOrder constructor copies workspace order logarithm positive,?_,?_,?_⟩
    · intro word
      obtain ⟨deadline,all⟩ := SpaceDecision.bounded_termination constructor source.program copies
        (decisionData word) (workspace word.length) (bounded word) (terminates word)
      exact ⟨deadline,all⟩
    · intro word
      exact SpaceDecision.spaceBound constructor source.program copies (decisionData word) (workspace word.length)
        (bounded word) (terminates word)
    · intro word
      change (∃ choices result ticks,(SpaceDecision.bank constructor.machine.program source.program copies).Executes
        (decisionData word) choices (SpaceDecision.bank constructor.machine.program source.program copies).initialConfiguration ticks (.accepted result)) ↔ word∈language
      rw [show (∃ choices result ticks,(SpaceDecision.bank constructor.machine.program source.program copies).Executes
          (decisionData word) choices (SpaceDecision.bank constructor.machine.program source.program copies).initialConfiguration ticks (.accepted result)) ↔
          (∃ choices ticks result,(SpaceDecision.bank constructor.machine.program source.program copies).Executes
            (decisionData word) choices (SpaceDecision.bank constructor.machine.program source.program copies).initialConfiguration ticks (.accepted result)) from
            ⟨fun ⟨choices,result,ticks,run⟩=>⟨choices,ticks,result,run⟩,
              fun ⟨choices,ticks,result,run⟩=>⟨choices,result,ticks,run⟩⟩]
      rw [SpaceDecision.accepted_iff constructor source.program copies word (workspace word.length)
        (bounded word) (terminates word) (enough word.length)]
      constructor
      · rintro ⟨choices,ticks,result,run⟩
        exact (correct word).mp ⟨choices,result,ticks,run⟩
      · intro member
        obtain ⟨choices,result,ticks,run⟩ := (correct word).mpr member
        exact ⟨choices,ticks,result,run⟩
  exact radiusNSPACE_subset_nspace α space positive radiusMember

end
end ComplexityOfGenerators.Multitape
