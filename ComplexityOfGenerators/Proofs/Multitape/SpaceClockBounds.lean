import ComplexityOfGenerators.Proofs.Multitape.SpaceResources
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Execution
import ComplexityOfGenerators.MultitapeSpaceConfigurations

namespace ComplexityOfGenerators.Multitape
open Simulation.TransducerBank
noncomputable section
variable {α : Type} {space : ℕ→ℕ}

/-- A fixed clock coefficient covers every finite source configuration graph.
The source control, alphabet and tape count are independent of this coefficient. -/
theorem exists_space_clock_copies (constructor : SpaceConstructor space)
    (source : MultitapeMachine α Bool Unit) (workspace : ℕ→ℕ) (order : ResourceOrder workspace space) :
    ∃ copies : ℕ, 0<copies ∧ ∀ n,
      SpaceConfigurations.clockWidth (Q:=source.Control) (S:=SpaceDecision.SourceSymbol constructor.machine.Work source.Work)
        (k:=source.tapes+(constructor.machine.tapes+1)) n (SpaceDecision.sourceRadius constructor (workspace n) n) ≤
          BinaryClockInitialisation.width (space:=space) copies n := by
  obtain ⟨base,positive,covers⟩ := ResourceOrder.global_affine order
  let coefficient := Fintype.card source.Control+
    2*(Fintype.card (SpaceDecision.SourceSymbol constructor.machine.Work source.Work)+1)*
      (source.tapes+(constructor.machine.tapes+1))+4
  let scale := base+constructor.constant+2
  refine ⟨coefficient*scale+1,by omega,?_⟩
  intro n
  have radius : SpaceDecision.sourceRadius constructor (workspace n) n+Nat.clog 2 (n+1)+1 ≤
      scale*(space n+Nat.clog 2 (n+1)+1) := by
    have bound := covers n
    dsimp [SpaceDecision.sourceRadius,scale]
    nlinarith
  calc
    _ ≤ coefficient*(SpaceDecision.sourceRadius constructor (workspace n) n+Nat.clog 2 (n+1)+1) :=
      SpaceConfigurations.clockWidth_linear n _
    _ ≤ coefficient*(scale*(space n+Nat.clog 2 (n+1)+1)) := Nat.mul_le_mul_left _ radius
    _ = (coefficient*scale)*(space n+Nat.clog 2 (n+1)+1) := by ac_rfl
    _ ≤ (coefficient*scale+1)*(space n+Nat.clog 2 (n+1)+1) := Nat.mul_le_mul_right _ (Nat.le_succ _)

theorem totalRadius_resourceOrder (constructor : SpaceConstructor space) (copies : ℕ)
    (workspace : ℕ→ℕ) (order : ResourceOrder workspace space)
    (logarithm : ResourceOrder (fun n=>Nat.clog 2 (n+1)) space)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n) :
    ResourceOrder (fun n=>SpaceDecision.totalRadius constructor copies (workspace n) n) space := by
  have first := (ResourceOrder.refl space).with_logarithmic_setup_of_bounds logarithm positive
    (constructor.constant+copies+20) (copies+20) (constructor.constant+copies+20)
  have firstEqual : (fun n=>BinaryClockInitialisation.radius constructor copies n)=
      (fun n=>(constructor.constant+copies+20)*space n+(copies+20)*Nat.clog 2 (n+1)+(constructor.constant+copies+20)) := by
    funext n
    dsimp [BinaryClockInitialisation.radius]
    ring
  rw [← firstEqual] at first
  have setup := (ResourceOrder.refl space).with_logarithmic_setup_of_bounds logarithm positive
    (constructor.constant+2*copies) (2*copies+1) (constructor.constant+2*copies+7)
  have second := order.add setup
  have secondEqual : (fun n=>SpaceDecision.sourceRadius constructor (workspace n) n+
        2*(BinaryClockInitialisation.width (space:=space) copies n+1)+4)=
      (fun n=>workspace n+((constructor.constant+2*copies)*space n+(2*copies+1)*Nat.clog 2 (n+1)+
        (constructor.constant+2*copies+7))) := by
    funext n
    dsimp [SpaceDecision.sourceRadius,BinaryClockInitialisation.width]
    ring
  rw [← secondEqual] at second
  obtain ⟨constant,threshold,positive,bound⟩ := first.add second
  refine ⟨constant,threshold,positive,?_⟩
  intro n large
  exact (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)).trans (bound n large)

end
end ComplexityOfGenerators.Multitape
