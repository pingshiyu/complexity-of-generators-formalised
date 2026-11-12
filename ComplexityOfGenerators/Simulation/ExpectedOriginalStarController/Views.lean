import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Basic

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

def factorSymbol : Cell M :=
  ExpectedStarCalls.pathSymbol emptyPhase (CertifiedStarPhase.encodePath M) .unit

@[simp] theorem pathWord_nil : pathWord M []=[] := rfl
@[simp] theorem pathWord_cons (j : ℕ) (parts : List ℕ) :
    pathWord M (j::parts) =
      ExpectedStarCalls.pathSymbol emptyPhase (CertifiedStarPhase.encodePath M) .cut ::
        List.replicate j (factorSymbol M) ++ pathWord M parts :=
  ExpectedStarCalls.pathWord_cons emptyPhase _ j parts

theorem parseFactor_eval (s : Store M) :
    (parseFactor M).eval s =
      (ExpectedStarCalls.parseFactor emptyPhase (CertifiedStarPhase.projectPath M)).eval s := rfl

theorem parseFactor_cost (s : Store M) :
    (parseFactor M).cost s =
      (ExpectedStarCalls.parseFactor emptyPhase (CertifiedStarPhase.projectPath M)).cost s := rfl

theorem prepareFactor_fields (s : Store M) (j : ℕ) (parts : List ℕ)
    (path : s 31=pathWord M (j::parts)) :
    (prepareFactor M).eval s 31=pathWord M parts ∧
      (prepareFactor M).eval s 71=List.replicate (j-1) (factorSymbol M) := by
  have fields := ExpectedStarCalls.parseFactor_fields emptyPhase
    (CertifiedStarPhase.encodePath M) (CertifiedStarPhase.projectPath M)
    (CertifiedStarPhase.project_encode M) s j parts path
  simp only [prepareFactor,Routine.seq,Routine.ofLocal,Local.eval_pop]
  constructor
  · simpa only [Function.update_of_ne (by decide : (31 : Fin 80)≠71),parseFactor_eval,pathWord] using fields.1
  · simpa only [Function.update_self,parseFactor_eval,fields.2,List.tail_replicate,factorSymbol] using
      (rfl : List.replicate (j-1) (factorSymbol M)=List.replicate (j-1) (factorSymbol M))

theorem prepareFactor_frame (s : Store M) (k : Fin 80) (path : k≠31) (factor : k≠71) :
    (prepareFactor M).eval s k=s k := by
  simp only [prepareFactor,Routine.seq,Routine.ofLocal,Local.eval_pop,Function.update_of_ne factor,parseFactor_eval]
  exact ExpectedStarCalls.parseFactor_frame emptyPhase (CertifiedStarPhase.projectPath M) s k path factor

theorem prepareFactor_bound (s : Store M) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepareFactor M).eval s) budget := by
  have parsed := ExpectedStarCalls.parseFactor_bound emptyPhase (CertifiedStarPhase.projectPath M) s budget sizes
  have bounded : StoreBound ((parseFactor M).eval s) budget := by simpa only [parseFactor_eval] using parsed
  change StoreBound (Function.update ((parseFactor M).eval s) 71 (((parseFactor M).eval s 71).tail)) budget
  apply bounded.update
  exact (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (bounded 71))

theorem prepareFactor_cost_le (s : Store M) (budget j : ℕ) (parts : List ℕ)
    (sizes : StoreBound s budget) (path : s 31=pathWord M (j::parts)) :
    (prepareFactor M).cost s≤12*(budget+1) := by
  have parsed := ExpectedStarCalls.parseFactor_cost emptyPhase
    (CertifiedStarPhase.encodePath M) (CertifiedStarPhase.projectPath M)
    (CertifiedStarPhase.project_encode M) s budget j parts sizes path
  change (parseFactor M).cost s+1+1≤_
  rw [parseFactor_cost]
  omega

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
