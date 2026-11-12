import ComplexityOfGenerators.Simulation.WordStack.OutputErasure

/-! Explicitly erased controller prefixes cannot emit call events, including
on finite tapes that exhaust inside a retry. -/
namespace ComplexityOfGenerators.Simulation.WordStack

def Instruction.NoEmit {Q S O : Type} : Instruction Q S O→Prop
  | .step _ _ _ output => output=none
  | _ => True

theorem Instruction.redirect_noEmit {Q Q' S O : Type} (f : Q→Q') (exit : Instruction Q' S O)
    (instruction : Instruction Q S O) (source : instruction.NoEmit) (target : exit.NoEmit) :
    (Instruction.redirect f exit instruction).NoEmit := by
  cases instruction <;> simp_all [Instruction.redirect,Instruction.NoEmit]

namespace Program
variable {Q S O : Type} {k : ℕ} (P : Program Q S O k)
def NoEmit : Prop := ∀ q cell index, (P.transition q cell index).NoEmit

theorem Steps.output_eq (pure : P.NoEmit) {n : ℕ} {bits : BitString}
    {start finish : Configuration Q S O k} {ticks : ℕ} (path : P.Steps n bits start ticks finish) :
    finish.output=start.output := by
  induction path with
  | refl => rfl
  | random source no yes bit t finish table lookup rest ih => exact ih
  | step source next action index emit t finish table rest ih =>
      have erased := pure source.state (source.store (P.select source.state)).head?
        (if source.indexHead<n then some () else none)
      rw [show P.transition source.state (source.store (P.select source.state)).head?
          (if source.indexHead<n then some () else none)=.step next action index emit from table] at erased
      change emit=none at erased
      subst emit
      simpa only [advance,Option.toList_none,List.append_nil] using ih

theorem Executes.exhausted_path {n : ℕ} {bits : BitString}
    {start : Configuration Q S O k} {ticks : ℕ} (run : P.Executes n bits start ticks .exhausted) :
    ∃ finish, P.Steps n bits start ticks finish ∧ ∃ no yes,
      P.instruction n finish=.random no yes ∧ bits[finish.randomHead]?=none := by
  generalize equality : Outcome.exhausted=result at run
  induction run with
  | accept source table => cases equality
  | reject source table => cases equality
  | exhausted source no yes table absent => exact ⟨source,.refl _,no,yes,table,absent⟩
  | random source no yes bit t result table lookup rest ih =>
      obtain ⟨finish,path,no',yes',terminal,absent⟩ := ih equality
      exact ⟨finish,.random _ _ _ _ _ _ table lookup path,no',yes',terminal,absent⟩
  | step source next action index emit t result table rest ih =>
      obtain ⟨finish,path,no,yes,terminal,absent⟩ := ih equality
      exact ⟨finish,.step _ _ _ _ _ _ _ table path,no,yes,terminal,absent⟩
end Program

namespace Command
variable {S O O' : Type} {k : ℕ}
inductive OutputFree : Command S O k→Prop
  | skip : OutputFree .skip
  | act (j action index) : OutputFree (.act j action index none)
  | branch (j next) (free : ∀ observation,OutputFree (next observation)) : OutputFree (.branch j next)
  | random {no yes} (left : OutputFree no) (right : OutputFree yes) : OutputFree (.random no yes)
  | seq {first second} (left : OutputFree first) (right : OutputFree second) : OutputFree (.seq first second)
  | loop (j test) {body} (free : OutputFree body) : OutputFree (.loop j test body)
  | drain : OutputFree .drain

theorem outputFree_erased (c : Command S O k) : OutputFree (c.filterMapOutput (fun _=>none : O→Option O')) := by
  induction c with
  | skip => exact .skip
  | act j action index output => cases output <;> exact .act _ _ _
  | branch j next ih => exact .branch _ _ ih
  | random no yes ihNo ihYes => exact .random ihNo ihYes
  | seq first second ihFirst ihSecond => exact .seq ihFirst ihSecond
  | loop j test body ih => exact .loop _ _ ih
  | drain => exact .drain

theorem OutputFree.noEmit {c : Command S O k} (pure : OutputFree c) (idle : Fin k) :
    (c.program idle).NoEmit := by
  induction pure with
  | skip => intro q cell index; trivial
  | act j action index => intro q cell input; cases q <;> trivial
  | branch j next free ih =>
      intro q cell index
      cases q with
      | none => rfl
      | some position =>
          obtain ⟨observation,q⟩ := position
          exact Instruction.redirect_noEmit _ _ _ (ih observation q cell index) trivial
  | random left right ihLeft ihRight =>
      intro q cell index
      cases q with
      | none => trivial
      | some position =>
          obtain ⟨bit,q⟩ := position
          cases bit
          · exact Instruction.redirect_noEmit _ _ _ (ihLeft q cell index) trivial
          · exact Instruction.redirect_noEmit _ _ _ (ihRight q cell index) trivial
  | seq left right ihLeft ihRight =>
      intro q cell index
      cases q with
      | inl q => exact Instruction.redirect_noEmit _ _ _ (ihLeft q cell index) rfl
      | inr q => exact Instruction.redirect_noEmit _ _ _ (ihRight q cell index) trivial
  | loop j test free ih =>
      intro q cell index
      cases q with
      | none => cases value : test (cell,index) <;> simp [program,Program.loop,value,Instruction.NoEmit]
      | some q => exact Instruction.redirect_noEmit _ _ _ (ih q cell index) rfl
  | drain => intro q cell index; trivial
end Command
end ComplexityOfGenerators.Simulation.WordStack
