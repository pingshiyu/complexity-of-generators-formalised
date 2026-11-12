import ComplexityOfGenerators.MultitapeComplexityClasses
import ComplexityOfGenerators.MultitapeSpace

/-! Space-class accounting on the actual finite bank model. Eventual
positivity absorbs the fixed number of tapes and initial work cells. -/

namespace ComplexityOfGenerators.Multitape

theorem ResourceOrder.affine {resource target : ℕ→ℕ} (bound : ResourceOrder resource target)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤target n) (scale offset : ℕ) :
    ResourceOrder (fun n => scale*resource n+offset) target := by
  obtain ⟨constant,threshold,_,bounded⟩ := bound
  obtain ⟨start,nonzero⟩ := positive
  refine ⟨scale*constant+offset+1,max threshold start,by omega,?_⟩
  intro n large
  have original := bounded n ((Nat.le_max_left _ _).trans large)
  have unit := nonzero n ((Nat.le_max_right _ _).trans large)
  calc
    scale*resource n+offset ≤ scale*(constant*target n)+offset :=
      Nat.add_le_add_right (Nat.mul_le_mul_left scale original) offset
    _ ≤ scale*(constant*target n)+offset*target n :=
      Nat.add_le_add_left (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left offset unit) _
    _ = (scale*constant+offset)*target n := by ring
    _ ≤ (scale*constant+offset+1)*target n := Nat.mul_le_mul_right _ (Nat.le_succ _)

variable (α : Type) [Fintype α]

/-- The radius convention used internally by the native bank compiler. -/
def RadiusNSPACE (space : ℕ→ℕ) : LanguageClass α :=
  {language | ∃ M : MultitapeMachine α Bool Unit, ∃ workspace : ℕ→ℕ,
    ResourceOrder workspace space ∧
    (∀ word,∃ time,M.TimeBound (decisionData word) time) ∧
    (∀ word,M.SpaceBound (decisionData word) (workspace word.length)) ∧
    ∀ word,(∃ bits,M.Accepts (decisionData word) bits) ↔ word∈language}

theorem nspace_subset_radiusNSPACE (space : ℕ→ℕ) : NSPACE α space⊆RadiusNSPACE α space := by
  rintro language ⟨machine,workspace,order,termination,bounded,correct⟩
  exact ⟨machine,workspace,order,termination,
    fun word => machine.radiusSpaceBound_of_cells _ _ (bounded word),correct⟩

theorem radiusNSPACE_subset_nspace (space : ℕ→ℕ)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n) : RadiusNSPACE α space⊆NSPACE α space := by
  rintro language ⟨machine,workspace,order,termination,bounded,correct⟩
  refine ⟨machine,(fun n => 2*machine.tapes*workspace n+machine.tapes),
    order.affine positive (2*machine.tapes) machine.tapes,termination,?_,correct⟩
  intro word
  have cells := machine.cellSpaceBound_of_radius (decisionData word) (workspace word.length) (bounded word)
  convert cells using 1 <;> ring

theorem nspace_eq_radiusNSPACE (space : ℕ→ℕ)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n) : NSPACE α space=RadiusNSPACE α space :=
  Set.Subset.antisymm (nspace_subset_radiusNSPACE α space) (radiusNSPACE_subset_nspace α space positive)

/-- The up-to generator class using implementation radii. Its generators and
their language prefixes are the same native bank machines. -/
def RadiusGSPACEUpTo (space : ℕ→ℕ) : LanguageClass α :=
  {language | ∃ G : UpToGeneratorFamily α,∃ workspace : ℕ→ℕ,
    G.toUniformGenerators.language=language ∧ ResourceOrder workspace space ∧
    ∀ n,G.machine.SpaceBound (generatorData n) (workspace n)}

theorem gspaceUpTo_subset_radiusGSPACEUpTo (space : ℕ→ℕ) : GSPACEUpTo α space⊆RadiusGSPACEUpTo α space := by
  rintro language ⟨family,workspace,same,order,bounded⟩
  exact ⟨family,workspace,same,order,fun n => family.machine.radiusSpaceBound_of_cells _ _ (bounded n)⟩

theorem radiusGSPACEUpTo_subset_gspaceUpTo (space : ℕ→ℕ)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n) : RadiusGSPACEUpTo α space⊆GSPACEUpTo α space := by
  rintro language ⟨family,workspace,same,order,bounded⟩
  refine ⟨family,(fun n => 2*family.machine.tapes*workspace n+family.machine.tapes),same,
    order.affine positive (2*family.machine.tapes) family.machine.tapes,?_⟩
  intro n
  have cells := family.machine.cellSpaceBound_of_radius (generatorData n) (workspace n) (bounded n)
  convert cells using 1 <;> ring

theorem gspaceUpTo_eq_radiusGSPACEUpTo (space : ℕ→ℕ)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n) : GSPACEUpTo α space=RadiusGSPACEUpTo α space :=
  Set.Subset.antisymm (gspaceUpTo_subset_radiusGSPACEUpTo α space)
    (radiusGSPACEUpTo_subset_gspaceUpTo α space positive)

end ComplexityOfGenerators.Multitape
