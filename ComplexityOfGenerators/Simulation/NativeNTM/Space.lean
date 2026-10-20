import ComplexityOfGenerators.Simulation.NativeNTM.ValidLoading
import ComplexityOfGenerators.Simulation.NativeNTM.Simulation
import ComplexityOfGenerators.Foundations.LibrarySavitch
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! Compose the native recognizer with library Savitch. No halting assumption
is imposed on the source, and no time or random-tape bound enters the result. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)

def language : Complexity.Language :=
  {full | ∃ c, (tm M).ReachesCfg ((tm M).initCfg full) c ∧ (tm M).halted c ∧ c.output.cells 1 = .one}

theorem encoded_mem_iff (word : List α) (s : ℕ) (space : M.SpaceBound (sourceData word) s) :
    encode word ∈ language M ↔ ∃ bits, M.Accepts (sourceData word) bits :=
  (encoded_init M word).accepting_iff.trans (simulated_accepts_iff M (encode word) word s space)

theorem reaches_from_halted {k : ℕ} {T : NTM k} {c d : Cfg k T.Q}
    (halt : T.halted c) (path : T.ReachesCfg c d) : d = c := by
  rcases path.cases_head with eq | ⟨_, ⟨live, _⟩, _⟩
  · exact eq.symm
  · exact (live halt).elim

theorem reachable_space (p : PolynomialBound)
    (space : ∀ word, M.SpaceBound (sourceData word) (p word.length))
    (full : BitString) (c : Cfg (Fintype.card (Tracks M)) (tm M).Q)
    (path : (tm M).ReachesCfg ((tm M).initCfg full) c) :
    c.WithinDecisionSpace full.length (full.length + p full.length + 1) := by
  obtain ⟨loaded, load, ready | reject⟩ := load_total M [] full [] 0 (by simp)
  all_goals
    simp only [List.nil_append, List.length_nil] at load
    have init := (boot_path M full).trans load
    rcases init.factor path with ⟨bound, _⟩ | after
    · exact bound.mono (by omega)
  · obtain ⟨word, length, rfl⟩ := ready
    have rep := reachable_represents M full word (p word.length) (space word) c after
    have mono : p word.length ≤ p full.length := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (by simpa using Nat.add_le_add_right length 1) _
    exact (represented_space M full word (p word.length) (space word) length c rep).mono (by omega)
  · simp only [List.nil_append] at reject
    have eq := reaches_from_halted reject.1 after
    rw [eq]
    exact reject.2.2.mono (by omega)

theorem language_mem_PSPACE (p : PolynomialBound)
    (space : ∀ word, M.SpaceBound (sourceData word) (p word.length)) :
    language M ∈ Complexity.PSPACE := by
  let q := Polynomial.X + p.asPolynomial + 1
  apply LibrarySavitch.reachability_mem_PSPACE (tm M) q
  intro full c path
  simpa [q] using reachable_space M p space full c path

end
end ComplexityOfGenerators.Simulation.NativeNTM
