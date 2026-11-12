import ComplexityOfGenerators.Simulation.NativeSourceCall.Cleanup.Packet
import ComplexityOfGenerators.Simulation.NativeSourceCall.Cleanup.Erase

/-! Accepted source calls restore blank transient tracks and return to the
controller origin, with a cost linear in the original visited interval. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem cleanup (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (c : Configuration (machine (F := F) M))
    (interval : ∃ lo hi : ℤ, lo≤0 ∧ 0≤hi ∧ visited=Finset.Icc lo hi)
    (inside : anchor∈visited) (blank : ∀ x, x∉visited → source x=none)
    (represented : State M data fixed source visited (packet length head anchor) .clearEnd anchor c) :
    ∃ ticks d, ticks≤2*length+4*visited.card+8 ∧
      State M data fixed (fun _ => none) ∅ (fun _ => none) .done 0 d ∧
      (machine M).Steps data bits c ticks d ∧ WorkFrame (machine M) c d := by
  obtain ⟨lo,hi,lower,upper,region⟩ := interval
  have anchorBounds : lo≤anchor ∧ anchor≤hi := by simpa only [region,Finset.mem_Icc] using inside
  have cardinality : (visited.card : ℤ)=hi+1-lo := by
    rw [region]
    exact Int.card_Icc_of_le (a:=lo) (b:=hi) (by omega)
  obtain ⟨start,startState,packetPath,packetFrame⟩ :=
    cleanup_packet M data bits fixed source visited length head anchor c represented
  let distance := (anchor-lo+1).toNat
  have distanceValue : (distance : ℤ)=anchor-lo+1 := Int.toNat_of_nonneg (by omega)
  obtain ⟨left,leftState,leftPath,leftFrame⟩ := startState.scan bits distance .left (lo-1)
    (fun t => anchor-t) (by simp) (by omega) (by intro t _; simp [Move.onInt]; omega) (by
      intro t before input auxiliary index
      rw [machine_transition]
      have mark : (read M (start.work (anchor-t))).visited=true := by
        rw [startState.memory]
        simp only [decide_eq_true_eq,region,Finset.mem_Icc]
        constructor <;> omega
      simp only [transition,mark,↓reduceIte])
  obtain ⟨first,firstState,turnPath,turnFrame⟩ := leftState.silent bits .cleanupRight .right (by
    have mark : (read M (left.work left.workHead)).visited=false := by
      rw [leftState.head,leftState.memory]
      simp only [region,Finset.mem_Icc]
      exact decide_eq_false (by omega)
    simp only [transition,mark,Bool.false_eq_true,↓reduceIte])
  have visitedInterval : visited=Finset.Ico lo (lo+(visited.card : ℤ)) := by
    rw [region]
    ext x
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    rw [← region]
    omega
  have firstReady : State M data fixed source (Finset.Ico lo (lo+(visited.card : ℤ)))
      (fun _ => none) .cleanupRight lo first := by
    rw [← visitedInterval]
    convert firstState using 1
    simp [Move.onInt]
  have outsideBlank : ∀ x, x∉Finset.Ico lo (lo+(visited.card : ℤ)) → source x=none := by
    simpa only [← visitedInterval] using blank
  obtain ⟨last,lastState,erasePath,eraseFrame⟩ := erase_interval M data bits fixed visited.card lo source outsideBlank first firstReady
  have lastReady : State M data fixed (fun _ => none) ∅ (fun _ => none) .cleanupOrigin hi last := by
    convert lastState using 1 <;> omega
  let rewind := hi.toNat
  have rewindValue : (rewind : ℤ)=hi := Int.toNat_of_nonneg upper
  obtain ⟨origin,originState,rewindPath,rewindFrame⟩ := lastReady.scan bits rewind .left 0
    (fun t => hi-t) (by simp) (by omega) (by intro t _; simp [Move.onInt]; omega) (by
      intro t before input auxiliary index
      rw [machine_transition]
      have mark : (read M (last.work (hi-t))).origin=false := by
        rw [lastReady.memory]
        exact decide_eq_false (by omega)
      simp only [transition,mark,Bool.false_eq_true,↓reduceIte])
  obtain ⟨done,doneState,donePath,doneFrame⟩ := originState.silent bits .done .stay (by
    simp only [transition,originState.head,originState.memory 0,decide_true,↓reduceIte])
  let ticks := (2*length+2)+distance+1+(visited.card+1)+rewind+1
  refine ⟨ticks,done,?_,?_,?_,?_⟩
  · dsimp only [ticks]
    omega
  · simpa only [Move.onInt] using doneState
  · exact ((((packetPath.trans (machine M) leftPath).trans (machine M) turnPath).trans
      (machine M) erasePath).trans (machine M) rewindPath).trans (machine M) donePath
  · exact ((((packetFrame.trans (machine M) leftFrame).trans (machine M) turnFrame).trans
      (machine M) eraseFrame).trans (machine M) rewindFrame).trans (machine M) doneFrame

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
