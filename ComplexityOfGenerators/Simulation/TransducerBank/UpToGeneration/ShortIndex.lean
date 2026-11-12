import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.Drain

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α Q S : Type} {k : ℕ} [Fintype α]
    (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

def shortConfiguration (position : ℕ) (phase : Control B fallback) :
    BankConfiguration α (Control B fallback) (Cell S α) (k+1) :=
  {(bank B fallback).initialConfiguration with state:=phase,indexHead:=position}

theorem short_advance (n position : ℕ) (phase next : Control B fallback) (move : Move) :
    (bank B fallback).advance (generatorData n) (shortConfiguration B fallback position phase) next
        (B.blank,none) .stay .stay .stay move none =
      shortConfiguration B fallback (move.onInput n position) next := by
  apply BankConfiguration.ext <;> try rfl
  all_goals simp [TapeBank.advance,shortConfiguration,TapeBank.initialConfiguration,bank,
    Move.onInput,Move.onInt,Function.update_eq_self]

theorem check_prefix (n position : ℕ) (fallbackBound : position≤fallback.length) (indexBound : position≤n)
    (choices : BitString) :
    (bank B fallback).Steps (generatorData n) choices (bank B fallback).initialConfiguration position
      (shortConfiguration B fallback position (.shortCheck ⟨position,by omega⟩)) := by
  induction position with
  | zero => exact .refl _
  | succ position ih =>
    have first := ih (by omega) (by omega)
    have table : (bank B fallback).instruction (generatorData n)
        (shortConfiguration B fallback position (.shortCheck ⟨position,by omega⟩))=
        .step (.shortCheck ⟨position+1,by omega⟩) (B.blank,none) .stay .stay .stay .right none := by
      simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData,
        show position<fallback.length by omega,show position<n by omega]
    have last := TapeBank.Steps.single (bank B fallback) (generatorData n) choices _ _ _ _ _ _ _ _ table
    rw [short_advance] at last
    have moved : Move.right.onInput n position=position+1 := by
      simp [Move.onInput,Nat.min_eq_left (show position+1≤n by omega)]
    rw [moved] at last
    exact first.trans (bank B fallback) last

theorem short_rewind (n position : ℕ) (fallbackBound : position≤fallback.length) (indexBound : position≤n)
    (choices : BitString) :
    (bank B fallback).Steps (generatorData n) choices
      (shortConfiguration B fallback position (.shortRewind ⟨position,by omega⟩)) position
      (shortConfiguration B fallback 0 (.shortRewind 0)) := by
  induction position with
  | zero => exact .refl _
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
    have first := TapeBank.Steps.single (bank B fallback) (generatorData n) choices _ _ _ _ _ _ _ _ table
    rw [short_advance] at first
    have moved : Move.left.onInput n (position+1)=position := by
      simp [Move.onInput]
    rw [moved] at first
    have remaining := ih (by omega) (by omega)
    simpa only [Nat.add_comm] using first.trans (bank B fallback) remaining

/-- Above the fixed shortest-word length, the native pretest and rewind take
exactly 2m+2 transitions and hand off to the real word chooser at index head0. -/
theorem long_index (n : ℕ) (long : fallback.length≤n) (choices : BitString) :
    (bank B fallback).Steps (generatorData n) choices (bank B fallback).initialConfiguration (2*fallback.length+2)
      {(bank B fallback).initialConfiguration with state:=.guess} := by
  have checked := check_prefix B fallback n fallback.length le_rfl long choices
  have table : (bank B fallback).instruction (generatorData n)
      (shortConfiguration B fallback fallback.length (.shortCheck ⟨fallback.length,by omega⟩))=
      .step (.shortRewind ⟨fallback.length,by omega⟩) (B.blank,none) .stay .stay .stay .stay none := by
    simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData]
  have switch := TapeBank.Steps.single (bank B fallback) (generatorData n) choices _ _ _ _ _ _ _ _ table
  rw [short_advance] at switch
  simp only [Move.onInput,Nat.min_eq_left long] at switch
  have rewound := short_rewind B fallback n fallback.length le_rfl long choices
  have finalTable : (bank B fallback).instruction (generatorData n) (shortConfiguration B fallback 0 (.shortRewind 0))=
      .step .guess (B.blank,none) .stay .stay .stay .stay none := by
    simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData]
  have final := TapeBank.Steps.single (bank B fallback) (generatorData n) choices _ _ _ _ _ _ _ _ finalTable
  rw [short_advance] at final
  have all := ((checked.trans (bank B fallback) switch).trans (bank B fallback) rewound).trans (bank B fallback) final
  simpa [shortConfiguration,TapeBank.initialConfiguration,Move.onInput,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,two_mul] using all

/-- A smaller index reaches the random drain before writing any word or
invoking the source decider. Every finite seed therefore exhausts. -/
theorem short_index (n : ℕ) (short : n<fallback.length) (choices : BitString) :
    ∃ ticks, ticks≤n+choices.length ∧
      (bank B fallback).Executes (generatorData n) choices (bank B fallback).initialConfiguration ticks .exhausted := by
  have checked := check_prefix B fallback n n (by omega) le_rfl choices
  have table : (bank B fallback).instruction (generatorData n)
      (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩))=.readRandom .drain .drain := by
    simp [TapeBank.instruction,bank,shortConfiguration,TapeBank.initialConfiguration,generatorData,short]
  cases choices with
  | nil =>
    have halt : (bank B fallback).Executes (generatorData n) []
        (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩)) 0 .exhausted :=
      .exhausted _ .drain .drain table rfl
    exact ⟨n,by simp,by simpa using checked.executes (bank B fallback) halt⟩
  | cons bit rest =>
    let after := TapeBank.choose (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩)) Phase.drain
    obtain ⟨ticks,budget,drained⟩ := TapeBank.drain_executes (bank B fallback) (generatorData n) (bit::rest) Phase.drain
      (by intros;rfl) rest.length after rfl (by simp [after,TapeBank.choose,shortConfiguration,TapeBank.initialConfiguration])
    have finish : (bank B fallback).Executes (generatorData n) (bit::rest)
        (shortConfiguration B fallback n (.shortCheck ⟨n,by omega⟩)) (ticks+1) .exhausted := by
      apply TapeBank.Executes.random _ Phase.drain Phase.drain bit ticks .exhausted table rfl
      cases bit <;> exact drained
    exact ⟨n+(ticks+1),by simp;omega,checked.executes (bank B fallback) finish⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
