import ComplexityOfGenerators.MultitapeModel
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! Radius and visited-cell accounting agree up to constants for an actual
finite tape bank. Positions are paired with their tape number, so visits to
different tapes are counted separately. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

def headWindow (radius : ℕ) : Finset (Fin k × ℤ) :=
  (Finset.univ : Finset (Fin k × Fin (2*radius+1))).image
    (fun coordinate => (coordinate.1,(coordinate.2.val : ℤ)-radius))

theorem mem_headWindow (radius : ℕ) (tape : Fin k) (position : ℤ) :
    (tape,position)∈headWindow (k := k) radius ↔ position.natAbs≤radius := by
  constructor
  · intro member
    obtain ⟨⟨j,index⟩,_,same⟩ := Finset.mem_image.mp member
    have equal := congrArg Prod.snd same
    dsimp only at equal
    have bound := index.isLt
    cases position <;> simp_all <;> omega
  · intro bounded
    have nonnegative : 0≤position+(radius : ℤ) := by cases position <;> simp_all <;> omega
    have small : (position+(radius : ℤ)).toNat<2*radius+1 := by cases position <;> simp_all <;> omega
    apply Finset.mem_image.mpr
    refine ⟨(tape,⟨(position+(radius : ℤ)).toNat,small⟩),Finset.mem_univ _,?_⟩
    apply Prod.ext
    · rfl
    · dsimp only; omega

theorem headWindow_card (radius : ℕ) : (headWindow (k := k) radius).card≤k*(2*radius+1) := by
  apply (Finset.card_image_le).trans
  simp

/-- Every work position visited on the fixed finite choice tape by time t.
The finite window is justified by the actual unit-step bank semantics. -/
noncomputable def visitedCells (data : InputData I A) (bits : BitString) (time : ℕ) : Finset (Fin k × ℤ) := by
  classical
  exact (headWindow time).filter fun coordinate =>
    ∃ ticks≤time, ∃ configuration, B.Steps data bits B.initialConfiguration ticks configuration ∧
      configuration.head coordinate.1=coordinate.2

theorem mem_visitedCells (data : InputData I A) (bits : BitString) (time : ℕ)
    (tape : Fin k) (position : ℤ) :
    (tape,position)∈B.visitedCells data bits time ↔
      ∃ ticks≤time, ∃ configuration, B.Steps data bits B.initialConfiguration ticks configuration ∧
        configuration.head tape=position := by
  classical
  constructor
  · intro member
    exact (Finset.mem_filter.mp member).2
  · intro reached
    apply Finset.mem_filter.mpr
    refine ⟨?_,reached⟩
    obtain ⟨ticks,small,configuration,path,located⟩ := reached
    have bounded := ((path.inRegion B 0 (B.initial_bounded data)).end_bound B).head tape
    simp only [Nat.zero_add] at bounded
    rw [mem_headWindow,← located]
    exact bounded.trans small

theorem advance_head_unit (data : InputData I A) (configuration : BankConfiguration O Q S k)
    (next write work input auxiliary index emit) (tape : Fin k) :
    (B.advance data configuration next write work input auxiliary index emit).head tape≤configuration.head tape+1 ∧
      configuration.head tape-1≤(B.advance data configuration next write work input auxiliary index emit).head tape := by
  by_cases selected : tape=B.select configuration.state
  · subst tape
    simp only [advance,Function.update_self]
    cases work <;> simp [Move.onInt] <;> omega
  · simp [advance,Function.update_of_ne selected]

/-- A unit-step head crosses every integral position between its endpoints.
This is proved for the real bank path, including random transitions. -/
theorem Steps.crosses {data : InputData I A} {bits : BitString} {time : ℕ}
    {source target : BankConfiguration O Q S k} (path : B.Steps data bits source time target)
    (tape : Fin k) (position : ℤ)
    (between : source.head tape≤position ∧ position≤target.head tape ∨
      target.head tape≤position ∧ position≤source.head tape) :
    ∃ ticks≤time, ∃ configuration, B.Steps data bits source ticks configuration ∧ configuration.head tape=position := by
  induction path with
  | refl source =>
      exact ⟨0,le_rfl,source,.refl _,by rcases between with between | between <;> omega⟩
  | random source no yes bit time target table lookup rest ih =>
      have nextBetween : (choose source (if bit then yes else no)).head tape≤position ∧ position≤target.head tape ∨
          target.head tape≤position ∧ position≤(choose source (if bit then yes else no)).head tape := by
        simpa only [choose] using between
      obtain ⟨ticks,small,configuration,earlier,located⟩ := ih nextBetween
      exact ⟨ticks+1,by omega,configuration,.random source no yes bit ticks configuration table lookup earlier,located⟩
  | step source next write work input auxiliary index emit time target table rest ih =>
      by_cases already : source.head tape=position
      · exact ⟨0,by omega,source,.refl _,already⟩
      · have unit := B.advance_head_unit data source next write work input auxiliary index emit tape
        have nextBetween :
            (B.advance data source next write work input auxiliary index emit).head tape≤position ∧ position≤target.head tape ∨
            target.head tape≤position ∧ position≤(B.advance data source next write work input auxiliary index emit).head tape := by
          rcases between with between | between
          · exact Or.inl ⟨by omega,between.2⟩
          · exact Or.inr ⟨between.1,by omega⟩
        obtain ⟨ticks,small,configuration,earlier,located⟩ := ih nextBetween
        exact ⟨ticks+1,by omega,configuration,
          .step source next write work input auxiliary index emit ticks configuration table earlier,located⟩

/-- The ordinary total count of visited work cells, uniformly over time and
all finite choice tapes. Read-only input tapes are excluded. -/
def CellSpaceBound (data : InputData I A) (space : ℕ) : Prop :=
  ∀ bits time, (B.visitedCells data bits time).card≤space

theorem cellSpaceBound_of_radius (data : InputData I A) (radius : ℕ) (bound : B.SpaceBound data radius) :
    B.CellSpaceBound data (k*(2*radius+1)) := by
  classical
  intro bits time
  apply (Finset.card_le_card (show B.visitedCells data bits time⊆headWindow radius from ?_)).trans
    (headWindow_card radius)
  rintro ⟨tape,position⟩ member
  obtain ⟨ticks,_,configuration,path,located⟩ := (B.mem_visitedCells data bits time tape position).mp member
  rw [mem_headWindow,← located]
  exact (bound bits ticks configuration path).head tape

def distanceCells (tape : Fin k) (position : ℤ) : Finset (Fin k × ℤ) :=
  (Finset.range (position.natAbs+1)).image
    (fun (index : ℕ) => (tape,if 0≤position then (index : ℤ) else -(index : ℤ)))

theorem distanceCells_card (tape : Fin k) (position : ℤ) :
    (distanceCells tape position).card=position.natAbs+1 := by
  classical
  rw [distanceCells,Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ same
    have equal := congrArg Prod.snd same
    dsimp only at equal
    split_ifs at equal <;> omega

theorem radius_le_visited {data : InputData I A} {bits : BitString} {time : ℕ}
    {configuration : BankConfiguration O Q S k} (path : B.Steps data bits B.initialConfiguration time configuration)
    (tape : Fin k) : (configuration.head tape).natAbs≤(B.visitedCells data bits time).card := by
  classical
  have subset : distanceCells tape (configuration.head tape)⊆B.visitedCells data bits time := by
    intro coordinate member
    obtain ⟨index,inside,rfl⟩ := Finset.mem_image.mp member
    have small : index≤(configuration.head tape).natAbs := by simpa using Finset.mem_range.mp inside
    have between : B.initialConfiguration.head tape≤
          (if 0≤configuration.head tape then (index : ℤ) else -(index : ℤ)) ∧
          (if 0≤configuration.head tape then (index : ℤ) else -(index : ℤ))≤configuration.head tape ∨
        configuration.head tape≤(if 0≤configuration.head tape then (index : ℤ) else -(index : ℤ)) ∧
          (if 0≤configuration.head tape then (index : ℤ) else -(index : ℤ))≤B.initialConfiguration.head tape := by
      simp only [initialConfiguration]
      cases position : configuration.head tape <;> simp_all <;> omega
    exact (B.mem_visitedCells data bits time _ _).mpr (path.crosses B tape _ between)
  have cardinal := Finset.card_le_card subset
  rw [distanceCells_card] at cardinal
  omega

theorem radiusSpaceBound_of_cells (data : InputData I A) (space : ℕ) (bound : B.CellSpaceBound data space) :
    B.SpaceBound data space := by
  intro bits time configuration path
  have readonly := (path.inRegion B 0 (B.initial_bounded data)).end_bound B
  exact ⟨readonly.input,readonly.auxiliary,readonly.index,
    fun tape => (B.radius_le_visited path tape).trans (bound bits time)⟩

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

namespace ComplexityOfGenerators.MultitapeMachine

open Simulation.TransducerBank

variable {I A O : Type} (M : MultitapeMachine I A O)

abbrev CellSpaceBound (data : InputData I A) (space : ℕ) : Prop := M.program.CellSpaceBound data space

theorem cellSpaceBound_of_radius (data : InputData I A) (radius : ℕ) (bound : M.SpaceBound data radius) :
    M.CellSpaceBound data (M.tapes*(2*radius+1)) := M.program.cellSpaceBound_of_radius data radius bound

theorem radiusSpaceBound_of_cells (data : InputData I A) (space : ℕ) (bound : M.CellSpaceBound data space) :
    M.SpaceBound data space := M.program.radiusSpaceBound_of_cells data space bound

theorem spaceBound_toNative [Fintype I] [Fintype A] [Fintype O]
    (data : InputData I A) (space : ℕ) (bound : M.SpaceBound data space) (terminates : M.Terminates data) :
    M.toNative.SpaceBound data (2*space+1) := bankMachine_spaceBound M.program data space bound terminates

end ComplexityOfGenerators.MultitapeMachine
