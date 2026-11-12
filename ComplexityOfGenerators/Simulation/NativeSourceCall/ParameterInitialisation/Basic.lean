import ComplexityOfGenerators.Simulation.NativeSourceCall.State

/-! Actual preparation of a unary virtual-index packet from a fixed caller
track. This routine uses no random bits and leaves the suspended caller's fixed
track and read-only context untouched. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Phase | first | scan | rewind | done
  deriving DecidableEq, Fintype

variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O) (parameter : F → Bool)

def control : Phase ≃ Fin (Fintype.card Phase) := Fintype.equivFin _

def transition (phase : Phase) (raw : Option (Fin (Fintype.card (Cell F M.symbols)))) :
    Instruction O (Fintype.card Phase) (Fintype.card (Cell F M.symbols)) :=
  let cell := read M raw
  let silent := fun next move => Instruction.step (control next) none move .stay .stay .stay none
  let write := fun next cell move => Instruction.step (control next)
    (some (alphabet M cell)) move .stay .stay .stay none
  match phase with
  | .first =>
      let live := parameter cell.fixed
      write (if live then .scan else .done)
        {cell with origin := true, visited := true, packet := some ⟨true, !live, true⟩}
        (if live then .right else .stay)
  | .scan =>
      let live := parameter cell.fixed
      write (if live then .scan else .rewind)
        {cell with packet := some ⟨false, !live, false⟩}
        (if live then .right else .stay)
  | .rewind =>
      if cell.packet.any IndexMark.first then silent .done .stay
      else silent .rewind .left
  | .done => .accept

def routine : Routine Unit Bool O (Fintype.card (Cell F M.symbols)) where
  states := Fintype.card Phase
  initial := control .first
  transition := fun state _ _ _ raw => transition M parameter (control.symm state) raw

def machine : Machine Unit Bool O := (routine M parameter).machine

@[simp] theorem machine_transition (phase : Phase) (input auxiliary index raw) :
    (machine M parameter).transition (control phase) input auxiliary index raw =
      transition M parameter phase raw := by
  simp [machine, routine, Routine.machine]

/-- The caller may already have installed the unique origin marker. -/
def BlankMemory (fixed : ℤ → F) (origin : Bool)
    (memory : ℤ → Option (Fin (Fintype.card (Cell F M.symbols)))) : Prop :=
  ∀ x, read M (memory x) = ⟨fixed x, none, origin && decide (x=0), false, none⟩

/-- Exactly the first `count` cells of the final packet have been written. -/
def packetPrefix (length count : ℕ) (x : ℤ) : Option IndexMark :=
  if x < count then packet length 0 0 x else none

theorem packetPrefix_zero (length : ℕ) : packetPrefix length 0 = fun _ => none := by
  funext x
  simp only [packetPrefix]
  split_ifs with before
  · simp [packet]; omega
  · rfl

theorem packetPrefix_complete (length : ℕ) : packetPrefix length (length+1) = packet length 0 0 := by
  funext x
  unfold packetPrefix
  split_ifs with before
  · rfl
  · simp [packet]; omega

theorem packetPrefix_write (length count : ℕ) (within : count≤length) :
    Function.update (packetPrefix length count) (count : ℤ)
      (some ⟨decide (count=0), decide (count=length), decide (count=0)⟩) =
      packetPrefix length (count+1) := by
  funext x
  by_cases same : x=(count : ℤ)
  · subst x
    simp only [Function.update_self, packetPrefix]
    have before : (count : ℤ)<(count+1 : ℕ) := by omega
    rw [if_pos before]
    simpa using (packet_at length 0 count 0 within).symm
  · rw [Function.update_of_ne same]
    unfold packetPrefix
    by_cases before : x<(count : ℤ)
    · rw [if_pos before, if_pos (by omega)]
    · rw [if_neg before, if_neg (by omega)]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
