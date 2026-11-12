import ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns.Graph

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
set_option backward.isDefEq.respectTransparency false
variable {I O Q S : Type} {k : ℕ}

theorem instruction_snapshot (source : TapeBank I Bool O Q S k) (word : List I)
    (c : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded (decisionData word) radius c) :
    instruction source word (snapshot c)=source.instruction (decisionData word) c := by
  have auxiliary : c.auxiliaryHead=0 := by have bound:=bounded.auxiliary;simpa [decisionData] using bound
  have index : c.indexHead=0 := by have bound:=bounded.index;simpa [decisionData] using bound
  simp only [instruction,TapeBank.instruction,snapshot,Snapshot.restore,auxiliary,index]

/-- Every actual accepting execution has a walk in the bounded finite graph. -/
theorem accepted_reachable (source : TapeBank I Bool O Q S k) (word : List I) (choices : BitString) (radius : ℕ)
    {c : BankConfiguration O Q S k} {ticks : ℕ} {result : List O}
    (run : source.Executes (decisionData word) choices c ticks (.accepted result))
    (valid : Valid source.blank word.length radius (snapshot c))
    (allBound : ∀ time finish, source.Steps (decisionData word) choices c time finish →
      source.Bounded (decisionData word) radius finish) :
    ∃ target : Vertex (Q:=Q) (k:=k) source.blank word.length radius,
      Relation.ReflTransGen (Edge source word radius) ⟨snapshot c,valid⟩ target ∧
        instruction source word target.val=.accept := by
  generalize accepted : Outcome.accepted result=outcome at run
  revert valid allBound accepted
  induction run with
  | accept c table =>
    intro valid allBound accepted
    exact ⟨⟨snapshot c,valid⟩,.refl,by rw [instruction_snapshot source word c radius (allBound 0 c (.refl _))];exact table⟩
  | reject c table => intro valid allBound accepted;cases accepted
  | exhausted c no yes table absent => intro valid allBound accepted;cases accepted
  | random c no yes bit ticks result table lookup rest ih =>
    intro valid allBound accepted
    let next := TapeBank.choose c (if bit then yes else no)
    have first : source.Steps (decisionData word) choices c 1 next :=
      .random c no yes bit 0 next table lookup (.refl _)
    have nextAll : ∀ time finish, source.Steps (decisionData word) choices next time finish →
        source.Bounded (decisionData word) radius finish := fun _ _ path => allBound _ _ (first.trans source path)
    have nextValid : Valid source.blank word.length radius (snapshot next) :=
      ⟨valid.input,valid.head,valid.outside⟩
    obtain ⟨target,path,accept⟩ := ih nextValid nextAll accepted
    refine ⟨target,path.head ?_,accept⟩
    exact Or.inl ⟨no,yes,bit,by rw [instruction_snapshot source word c radius (allBound 0 c (.refl _))];exact table,rfl⟩
  | step c next write work input auxiliary index emit ticks result table rest ih =>
    intro valid allBound accepted
    let after := source.advance (decisionData word) c next write work input auxiliary index emit
    have first : source.Steps (decisionData word) choices c 1 after :=
      .step c next write work input auxiliary index emit 0 after table (.refl _)
    have afterAll : ∀ time finish, source.Steps (decisionData word) choices after time finish →
        source.Bounded (decisionData word) radius finish := fun _ _ path => allBound _ _ (first.trans source path)
    have bound := allBound 1 after first
    have outside := advance_outside source word (snapshot c) radius valid next write work input auxiliary index emit
    have afterValid : Valid source.blank word.length radius (snapshot after) :=
      ⟨bound.input,bound.head,outside⟩
    obtain ⟨target,path,accept⟩ := ih afterValid afterAll accepted
    refine ⟨target,path.head ?_,accept⟩
    exact Or.inr ⟨next,write,work,input,auxiliary,index,emit,
      by rw [instruction_snapshot source word c radius (allBound 0 c (.refl _))];exact table,rfl⟩

end ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
