import ComplexityOfGenerators.Simulation.StarPaths.Proposal

namespace ComplexityOfGenerators.Simulation.StarPaths
set_option backward.isDefEq.respectTransparency false

def allowed (flags : List Bool) (parts : Parts) : Bool :=
  parts.all (fun j => decide (0 < j) && (flags[j-1]?).getD false)

@[simp] theorem allowed_iff (flags : List Bool) (parts : Parts) :
    allowed flags parts = true ↔ ∀ j ∈ parts, certified flags j := by
  simp [allowed,certified]

/-- Invalid random proposals are replaced by the deterministic DP witness.
The path-selection phase never rejects a productive target. -/
def selected (flags : List Bool) (n : ℕ) (bits : List Bool) : Option Parts :=
  let parts := proposal n bits
  if allowed flags parts then some parts else fallback flags n

theorem selected_sound (flags : List Bool) (n : ℕ) (bits : List Bool) (parts : Parts)
    (result : selected flags n bits = some parts) : Valid flags n parts := by
  unfold selected at result
  dsimp only at result
  split_ifs at result with valid
  · have equal : proposal n bits = parts := Option.some.inj result
    subst parts
    exact ⟨proposal_sum n bits,(allowed_iff flags _).mp valid⟩
  · exact (fallback_spec flags n).1 parts result

theorem selected_isSome (flags : List Bool) (n : ℕ) (bits : List Bool) :
    (selected flags n bits).isSome = true ↔ ∃ parts, Valid flags n parts := by
  constructor
  · intro present
    obtain ⟨parts,result⟩ := Option.isSome_iff_exists.mp present
    exact ⟨parts,selected_sound flags n bits parts result⟩
  · intro possible
    unfold selected
    dsimp only
    split_ifs
    · rfl
    · exact (fallback_spec flags n).2.mpr possible

theorem selected_full_support (flags : List Bool) (n : ℕ) (parts : Parts) (valid : Valid flags n parts) :
    ∃ bits : List Bool, bits.length = n-1 ∧ selected flags n bits = some parts := by
  obtain ⟨bits,length,result⟩ := proposal_full_support n parts valid.1 (fun j member => (valid.2 j member).1)
  refine ⟨bits,length,?_⟩
  simp [selected,result,(allowed_iff flags parts).mpr valid.2]

@[simp] theorem selected_zero (flags : List Bool) (bits : List Bool) : selected flags 0 bits = some [] := by
  simp [selected,proposal,allowed]

end ComplexityOfGenerators.Simulation.StarPaths
