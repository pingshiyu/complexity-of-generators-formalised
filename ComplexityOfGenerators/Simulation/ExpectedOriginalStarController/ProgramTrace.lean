import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Loop
import ComplexityOfGenerators.Simulation.WordStack.EventReturns

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

def allowed (_ : Unit) (j : ℕ) : Prop := 0<j

theorem Trace.eventReturns {n : ℕ} {bits : BitString} {parts : List ℕ}
    {start finish : Memory (Cell M) Unit 80} (trace : Trace M n bits parts start finish) :
    start.indexHead=0 → start.store 31=pathWord M parts → (∀ j∈parts,0<j) →
      ((loop M).program 0).EventReturns 0 71 (factorSymbol M) allowed n bits
        (parts.map (fun j=>((),j))) start finish := by
  induction trace with
  | nil m =>
      intro origin path _
      refine ⟨none,.nil _ _ 0 (.refl _) rfl,?_⟩
      simp [Program.instruction,Command.program,loop,Program.loop,path,Memory.at,Configuration.mapState]
  | cons j parts m finish ticks prepared ready rest ih =>
      intro origin path positive
      let A := (prepareFactor M).command.program 0
      let E := (event M).program 0
      let B := A.sequence E
      let L := B.loop 31 (fun cell _=>cell.isSome)
      change L.EventReturns 0 71 (factorSymbol M) allowed n bits (((),j)::parts.map (fun i=>((),i))) m finish
      obtain ⟨q,preparePath,prepareAccept⟩ := prepared.compiled 0 (by omega)
      obtain ⟨r,tailTrace,tailAccept⟩ := ih ready.origin ready.path
        (fun i member=>positive i (by simp [member]))
      have enter : L.Steps n bits (m.at none) 1 (m.at (some (.inl A.initial))) := by
        apply Program.Steps.go_at _ n bits m _ _ (by omega)
        simp [L,Program.instruction,Program.loop,path,pathWord_cons,Memory.at,Configuration.mapState,B,Program.sequence]
      have embedded := ((A.sequence_left E).trans (B.loop_body 31 (fun cell _=>cell.isSome))).steps A preparePath
      have transfer : L.Steps n bits ((afterFactor M m).at (some (.inl q))) 1
          ((afterFactor M m).at (some (.inr E.initial))) := by
        apply Program.Steps.go_at _ n bits (afterFactor M m) _ _ (by simpa [afterFactor] using (show m.indexHead≤n by omega))
        change Instruction.redirect some (.step none .stay .stay none)
          (Instruction.redirect Sum.inl (.step (.inr E.initial) .stay .stay none)
            (A.instruction n ((afterFactor M m).at q))) = _
        rw [prepareAccept]
        rfl
      let before : WordStack.Configuration (loop M).Control (Cell M) Unit 80 := (afterFactor M m).at (some (.inr E.initial))
      have initialEvent : E.initial=false := rfl
      have table : L.instruction n before=.step (some (.inr true)) .stay .stay (some ()) := rfl
      have advanced : L.advance n before (some (.inr true)) .stay .stay (some ()) =
          (afterEvent M (afterFactor M m)).at (some (.inr true)) := by
        apply Configuration.ext <;> try rfl
        · simpa [Program.advance,Move.onInput,before,Memory.at,Configuration.mapState,afterEvent] using
            (Nat.min_eq_left (show (afterFactor M m).indexHead≤n by simpa [afterFactor] using (show m.indexHead≤n by omega)))
        · simp [L,B,E,event,Command.program,Program.advance,Program.loop,Program.sequence,Program.atom,
            before,Memory.at,Configuration.mapState,Action.apply,afterEvent,Function.update_eq_self]
      have returned : L.Steps n bits
          ((afterEvent M (afterFactor M m)).at (some (.inr true))) 1
          ((afterEvent M (afterFactor M m)).at none) := by
        apply Program.Steps.go_at _ n bits (afterEvent M (afterFactor M m)) _ _ (by simpa [afterEvent,afterFactor] using (show m.indexHead≤n by omega))
        rfl
      have actualTail : L.EventTrace 0 71 (factorSymbol M) allowed n bits (parts.map (fun i=>((),i)))
          (L.advance n before (some (.inr true)) .stay .stay (some ())) (finish.at r) := by
        rw [advanced]
        exact tailTrace.prepend returned rfl
      refine ⟨r,.cons () j _ _ before (some (.inr true)) _ _
        ((enter.trans L embedded).trans L transfer) rfl (positive j (by simp))
        rfl ready.eventRegister ready.exported table actualTail,tailAccept⟩

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
