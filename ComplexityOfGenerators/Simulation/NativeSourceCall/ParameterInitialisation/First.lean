import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.Scan

namespace ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O) (parameter : F → Bool)

def firstCell (fixed : ℤ → F) (length : ℕ) : Cell F M.symbols :=
  ⟨fixed 0,none,true,true,some ⟨true,decide (length=0),true⟩⟩

theorem first_memory (fixed : ℤ → F) (length : ℕ) (origin : Bool) (memory)
    (blank : BlankMemory M fixed origin memory) :
    Memory M fixed (fun _=>none) {0} (packetPrefix length 1)
      (Function.update memory 0 (some (alphabet M (firstCell M fixed length)))) := by
  intro x
  by_cases zero : x=0
  · subst x
    simp [firstCell, packetPrefix, packet]
    omega
  · rw [Function.update_of_ne zero, blank x]
    have outside : packetPrefix length 1 x=none := by
      unfold packetPrefix
      split_ifs with before
      · simp [packet]; omega
      · rfl
    simp [outside, zero]

theorem first_step (data : InputData Unit Bool) (bits : BitString) (fixed : ℤ → F)
    (length : ℕ) (origin : Bool) (unary : Unary parameter fixed length)
    (c : Configuration (machine M parameter))
    (blank : BlankMemory M fixed origin c.work) (initial : c.state=control .first)
    (atOrigin : c.workHead=0) (bounds : ReadHeadBounds (machine M parameter) data c) :
    ∃ d, State M parameter data fixed {0} (packetPrefix length 1)
        (if length=0 then .done else .scan) (if length=0 then 0 else 1) d ∧
      (machine M parameter).Steps data bits c 1 d ∧ WorkFrame (machine M parameter) c d := by
  let next := if length=0 then Phase.done else .scan
  let move := if length=0 then Move.stay else .right
  let d := advance M parameter data c next (some (firstCell M fixed length)) move
  have table : transition M parameter .first (c.work c.workHead) =
      .step (control next) (some (alphabet M (firstCell M fixed length)))
        move .stay .stay .stay none := by
    rw [atOrigin]
    have live : parameter (fixed 0) = decide (0<length) := by simpa using unary 0
    cases length with
    | zero => simp [next,move,transition,firstCell,blank 0,live]
    | succ length => simp [next,move,transition,firstCell,blank 0,live]
  refine ⟨d,⟨?_,rfl,?_,?_⟩,
    advance_path M parameter data bits c .first next (some (firstCell M fixed length)) move initial table,
    advance_frame M parameter data c next (some (firstCell M fixed length)) move bounds⟩
  · change Memory M fixed (fun _=>none) {0} (packetPrefix length 1)
      (Function.update c.work c.workHead (some (alphabet M (firstCell M fixed length))))
    rw [atOrigin]
    exact first_memory M fixed length origin c.work blank
  · change move.onInt c.workHead = _
    rw [atOrigin]
    cases length <;> rfl
  · exact bounds.stepConfiguration (machine M parameter) data c _ _ _ _ _ _ _

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
