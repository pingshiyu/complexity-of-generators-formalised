import ComplexityOfGenerators.Simulation.WordStack.EventReturns

namespace ComplexityOfGenerators.Simulation.WordStack.Program
set_option backward.isDefEq.respectTransparency false
variable {Q Q' S E : Type} {k : ℕ} {P : Program Q S E k}
    {slot exported : Fin k} {symbol : S} {Allowed : E→ℕ→Prop}
    {n : ℕ} {bits : BitString} {events more : List (E×ℕ)}

theorem EventTrace.append {start middle finish : Configuration Q S E k}
    (first : P.EventTrace slot exported symbol Allowed n bits events start middle)
    (second : P.EventTrace slot exported symbol Allowed n bits more middle finish) :
    P.EventTrace slot exported symbol Allowed n bits (events++more) start finish := by
  induction first with
  | nil start middle ticks path silent => exact second.prepend path silent
  | cons e j events start before next middle ticks segment silent allowed selected empty parameter event rest ih =>
      exact .cons _ _ _ _ _ _ _ _ segment silent allowed selected empty parameter event (ih second)

theorem EventReturns.sequence {T : Program Q' S E k} {start middle finish : Memory S E k}
    (first : P.EventReturns slot exported symbol Allowed n bits events start middle)
    (second : T.EventReturns slot exported symbol Allowed n bits more middle finish)
    (bounded : start.indexHead≤n) :
    (P.sequence T).EventReturns slot exported symbol Allowed n bits (events++more) start finish := by
  obtain ⟨q,left,terminal⟩ := first
  obtain ⟨r,right,halt⟩ := second
  obtain ⟨_,leftPath⟩ := left.steps
  have middleBound := leftPath.index_le P bounded
  have mappedLeft := left.embeds (P.sequence_left T)
  have mappedRight := right.embeds (P.sequence_right T)
  have transfer : (P.sequence T).Steps n bits (middle.at (.inl q)) 1 (middle.at (.inr T.initial)) := by
    apply Steps.go_at _ n bits middle _ _ middleBound
    change Instruction.redirect Sum.inl _ (P.instruction n (middle.at q)) = _
    rw [terminal]; rfl
  refine ⟨.inr r,mappedLeft.append (mappedRight.prepend transfer rfl),?_⟩
  change Instruction.redirect Sum.inr .accept (T.instruction n (finish.at r)) = _
  rw [halt]; rfl

theorem EventReturns.branch {B : Type} {States : B→Type} (j : Fin k)
    (choose : Option S→Option Unit→B) (body : (b : B)→Program (States b) S E k)
    {start finish : Memory S E k} (bounded : start.indexHead≤n)
    (run : (body (choose (start.store j).head? (if start.indexHead<n then some () else none))).EventReturns
      slot exported symbol Allowed n bits events start finish) :
    (Program.branch j choose body).EventReturns slot exported symbol Allowed n bits events start finish := by
  let b := choose (start.store j).head? (if start.indexHead<n then some () else none)
  obtain ⟨q,trace,terminal⟩ := run
  have enter : (Program.branch j choose body).Steps n bits (start.at none) 1
      (start.at (some ⟨b,(body b).initial⟩)) := by
    apply Steps.go_at _ n bits start _ _ bounded
    rfl
  have mapped := trace.embeds (branch_body j choose body b)
  refine ⟨some ⟨b,q⟩,mapped.prepend enter rfl,?_⟩
  change Instruction.redirect (fun r : States b=>(some ⟨b,r⟩ : Option (Sigma States))) .accept ((body b).instruction n (finish.at q)) = _
  rw [terminal]; rfl

end ComplexityOfGenerators.Simulation.WordStack.Program
