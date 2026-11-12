import ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
set_option backward.isDefEq.respectTransparency false
variable {I O Q S : Type} {k : ℕ}

/-- The exact source instruction ignores random position and accumulated output. -/
def instruction (source : TapeBank I Bool O Q S k) (word : List I) (c : Snapshot Q S k) : BankInstruction Q S O :=
  source.instruction (decisionData word) (c.restore 0 [])

theorem instruction_restore (source : TapeBank I Bool O Q S k) (word : List I)
    (c : Snapshot Q S k) (random : ℕ) (output : List O) :
    source.instruction (decisionData word) (c.restore random output)=instruction source word c := rfl

def advance (source : TapeBank I Bool O Q S k) (word : List I) (c : Snapshot Q S k)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O) : Snapshot Q S k :=
  snapshot (source.advance (decisionData word) (c.restore 0 []) next write work input auxiliary index emit)

theorem advance_restore (source : TapeBank I Bool O Q S k) (word : List I)
    (c : Snapshot Q S k) (random : ℕ) (output : List O) (next write work input auxiliary index emit) :
    source.advance (decisionData word) (c.restore random output) next write work input auxiliary index emit=
      (advance source word c next write work input auxiliary index emit).restore random (output++emit.toList) := by
  apply BankConfiguration.ext <;> try rfl
  all_goals cases auxiliary <;> cases index <;>
    simp [advance,snapshot,Snapshot.restore,TapeBank.advance,decisionData,Move.onInput]

theorem choose_restore (c : Snapshot Q S k) (random : ℕ) (output : List O) (next : Q) :
    TapeBank.choose (c.restore random output) next=({c with state:=next}).restore (random+1) output := rfl

def Next (source : TapeBank I Bool O Q S k) (word : List I) (first second : Snapshot Q S k) : Prop :=
  (∃ (no yes : Q) (bit : Bool), instruction source word first=.readRandom no yes ∧
    second={first with state:=if bit then yes else no}) ∨
  (∃ next write work input auxiliary index emit,
    instruction source word first=.step next write work input auxiliary index emit ∧
    second=advance source word first next write work input auxiliary index emit)

abbrev Edge (source : TapeBank I Bool O Q S k) (word : List I) (radius : ℕ) :=
  fun first second : Vertex (Q:=Q) (k:=k) source.blank word.length radius => Next source word first.val second.val

theorem advance_outside (source : TapeBank I Bool O Q S k) (word : List I)
    (c : Snapshot Q S k) (radius : ℕ) (valid : Valid source.blank word.length radius c)
    (next write work input auxiliary index emit) :
    ∀ j position, radius<position.natAbs →
      (advance source word c next write work input auxiliary index emit).tape j position=source.blank := by
  intro j position outside
  simp only [advance,snapshot,TapeBank.advance,Snapshot.restore]
  by_cases selected : j=source.select c.state
  · subst j
    rw [Function.update_self]
    have different : position≠c.head (source.select c.state) := by
      intro same
      have bound := valid.head (source.select c.state)
      rw [same] at outside
      omega
    rw [Function.update_of_ne different]
    exact valid.outside _ _ outside
  · rw [Function.update_of_ne selected]
    exact valid.outside _ _ outside

/-- Every finite walk in the graph replays as an actual native source run,
with one transition per edge and a concrete finite choice tape. The arbitrary
seedPrefix permits random reads to be composed without assuming a reset oracle. -/
theorem replay_chain (source : TapeBank I Bool O Q S k) (word : List I)
    (tail : List (Snapshot Q S k)) (start : Snapshot Q S k)
    (chain : (start::tail).IsChain (Next source word))
    (terminal : instruction source word ((start::tail).getLast (by simp))=.accept)
    (seedPrefix : BitString) (output : List O) :
    ∃ suffix result, source.Executes (decisionData word) (seedPrefix++suffix)
      (start.restore seedPrefix.length output) tail.length (.accepted result) := by
  induction tail generalizing start seedPrefix output with
  | nil =>
    refine ⟨[],output,?_⟩
    apply TapeBank.Executes.accept
    simpa only [instruction_restore,List.getLast_singleton] using terminal
  | cons next rest ih =>
    obtain ⟨edge,remaining⟩ := List.isChain_cons_cons.mp chain
    have last : instruction source word ((next::rest).getLast (by simp))=.accept := by simpa using terminal
    rcases edge with ⟨no,yes,bit,table,equal⟩ | ⟨state,write,work,input,auxiliary,index,emit,table,equal⟩
    · obtain ⟨suffix,result,run⟩ := ih next remaining last (seedPrefix++[bit]) output
      refine ⟨bit::suffix,result,?_⟩
      apply TapeBank.Executes.random _ no yes bit rest.length _
      · rw [instruction_restore,table]
      · change (seedPrefix++bit::suffix)[seedPrefix.length]?=some bit
        rw [List.getElem?_append_right (Nat.le_refl seedPrefix.length)]
        simp
      · have shifted : source.Executes (decisionData word) (seedPrefix++bit::suffix)
            (next.restore (seedPrefix.length+1) output) rest.length (.accepted result) := by
          simpa [List.append_assoc] using run
        rw [choose_restore,← equal]
        exact shifted
    · obtain ⟨suffix,result,run⟩ := ih next remaining last seedPrefix (output++emit.toList)
      refine ⟨suffix,result,?_⟩
      apply TapeBank.Executes.step _ state write work input auxiliary index emit rest.length _
      · rw [instruction_restore,table]
      · rw [advance_restore,← equal]
        exact run

end ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
