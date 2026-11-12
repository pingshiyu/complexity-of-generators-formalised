import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.ShortIndex
import ComplexityOfGenerators.Simulation.TransducerBank.RegionDrain

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α Q S : Type} {k : ℕ} [Fintype α]
    (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

theorem shortConfiguration_bounded (n position : ℕ) (phase : Control B fallback) (valid : position≤n) :
    (bank B fallback).Bounded (generatorData n) 0 (shortConfiguration B fallback position phase) := by
  constructor <;> simp [shortConfiguration,TapeBank.initialConfiguration,generatorData,valid]

theorem short_region_single (n position : ℕ) (choices : BitString) (phase next : Control B fallback) (move : Move)
    (valid : position≤n)
    (table : (bank B fallback).instruction (generatorData n) (shortConfiguration B fallback position phase)=
      .step next (B.blank,none) .stay .stay .stay move none) :
    (bank B fallback).RegionSteps (generatorData n) choices 0 (shortConfiguration B fallback position phase) 1
      (shortConfiguration B fallback (move.onInput n position) next) := by
  apply TapeBank.RegionSteps.step _ next (B.blank,none) .stay .stay .stay move none 0 _
    (shortConfiguration_bounded B fallback n position phase valid) table
  rw [short_advance]
  exact .refl _ (shortConfiguration_bounded B fallback n (move.onInput n position) next (move.onInput_le n position valid))

theorem check_prefix_region (n position : ℕ) (fallbackBound : position≤fallback.length) (indexBound : position≤n)
    (choices : BitString) :
    (bank B fallback).RegionSteps (generatorData n) choices 0 (bank B fallback).initialConfiguration position
      (shortConfiguration B fallback position (.shortCheck ⟨position,by omega⟩)) := by
  induction position with
  | zero => exact .refl _ (shortConfiguration_bounded B fallback n 0 (.shortCheck 0) (Nat.zero_le _))
  | succ position ih =>
    have first := ih (by omega) (by omega)
    have table : (bank B fallback).instruction (generatorData n)
        (shortConfiguration B fallback position (.shortCheck ⟨position,by omega⟩))=
        .step (.shortCheck ⟨position+1,by omega⟩) (B.blank,none) .stay .stay .stay .right none := by
      simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData,
        show position<fallback.length by omega,show position<n by omega]
    have last := short_region_single B fallback n position choices _ _ .right (by omega) table
    have moved : Move.right.onInput n position=position+1 := by
      simp [Move.onInput,Nat.min_eq_left (show position+1≤n by omega)]
    rw [moved] at last
    exact first.trans (bank B fallback) last

theorem short_rewind_region (n position : ℕ) (fallbackBound : position≤fallback.length) (indexBound : position≤n)
    (choices : BitString) :
    (bank B fallback).RegionSteps (generatorData n) choices 0
      (shortConfiguration B fallback position (.shortRewind ⟨position,by omega⟩)) position
      (shortConfiguration B fallback 0 (.shortRewind 0)) := by
  induction position with
  | zero => exact .refl _ (shortConfiguration_bounded B fallback n 0 (.shortRewind 0) (Nat.zero_le _))
  | succ position ih =>
    have table : (bank B fallback).instruction (generatorData n)
        (shortConfiguration B fallback (position+1) (.shortRewind ⟨position+1,by omega⟩))=
        .step (.shortRewind ⟨position,by omega⟩) (B.blank,none) .stay .stay .stay .left none := by
      simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData]
      split_ifs with positive
      · rfl
      · have strict : (0 : Fin (fallback.length+1)) < ⟨position+1,by omega⟩ := by
          change (0 : Fin (fallback.length+1)).val < position+1
          rw [show (0 : Fin (fallback.length+1)).val=0 by simp]
          omega
        exact False.elim (positive strict)
    have first := short_region_single B fallback n (position+1) choices _ _ .left (by omega) table
    simp only [Move.onInput,Nat.add_sub_cancel] at first
    simpa only [Nat.add_comm] using first.trans (bank B fallback) (ih (by omega) (by omega))

/-- The pretest uses no work-space radius, independently of n and seed length. -/
theorem long_index_region (n : ℕ) (long : fallback.length≤n) (choices : BitString) :
    (bank B fallback).RegionSteps (generatorData n) choices 0 (bank B fallback).initialConfiguration (2*fallback.length+2)
      {(bank B fallback).initialConfiguration with state:=.guess} := by
  have checked := check_prefix_region B fallback n fallback.length le_rfl long choices
  have switch := short_region_single B fallback n fallback.length choices
    (.shortCheck ⟨fallback.length,by omega⟩) (.shortRewind ⟨fallback.length,by omega⟩) .stay long (by
      simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData])
  simp only [Move.onInput,Nat.min_eq_left long] at switch
  have rewound := short_rewind_region B fallback n fallback.length le_rfl long choices
  have final := short_region_single B fallback n 0 choices (.shortRewind 0) .guess .stay (Nat.zero_le _) (by
      simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData])
  have all := ((checked.trans (bank B fallback) switch).trans (bank B fallback) rewound).trans (bank B fallback) final
  simpa [shortConfiguration,TapeBank.initialConfiguration,Move.onInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,two_mul] using all

theorem short_index_region (n : ℕ) (short : n<fallback.length) (choices : BitString) :
    (bank B fallback).RegionRun (generatorData n) choices 0 (bank B fallback).initialConfiguration .exhausted := by
  have checked := check_prefix_region B fallback n n (by omega) le_rfl choices
  have bounded := shortConfiguration_bounded B fallback n n (.shortCheck ⟨n,by omega⟩) le_rfl
  have table : (bank B fallback).instruction (generatorData n)
      (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩))=.readRandom .drain .drain := by
    simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData,short]
  cases choices with
  | nil => exact ⟨n,_,checked,.exhausted _ .drain .drain table rfl⟩
  | cons bit rest =>
    let after := TapeBank.choose (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩)) Phase.drain
    have afterBound : (bank B fallback).Bounded (generatorData n) 0 after :=
      ⟨bounded.input,bounded.auxiliary,bounded.index,bounded.head⟩
    have drained := TapeBank.drain_inRegion (bank B fallback) (generatorData n) (bit::rest) Phase.drain
      (by intros;rfl) rest.length after rfl
      (by simp [after,TapeBank.choose,shortConfiguration,TapeBank.initialConfiguration]) 0 afterBound
    have first : (bank B fallback).RegionSteps (generatorData n) (bit::rest) 0
        (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩)) 1 after := by
      apply TapeBank.RegionSteps.random _ Phase.drain Phase.drain bit 0 _ bounded table rfl
      cases bit <;> exact .refl _ afterBound
    exact (drained.prepend (bank B fallback) first).prepend (bank B fallback) checked

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
