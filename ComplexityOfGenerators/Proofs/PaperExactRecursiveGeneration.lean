import ComplexityOfGenerators.Proofs.PaperExactRecursiveSource
import ComplexityOfGenerators.Proofs.PaperExactRecursiveNormalization
import ComplexityOfGenerators.Proofs.PaperExactRecursiveLegacy
import ComplexityOfGenerators.Simulation.PaperFilteredInverse.PolynomialBounds

/-! Current Proposition6.2. The bounded-label, accepting-time inverse machines
are compiled into genuine all-label finite-trial machines, using the checked
native source and its primitive cost bounds. No compiler or trial-budget
hypothesis is added to the current paper's exact-recursive criterion. -/
namespace ComplexityOfGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Simulation

namespace PaperExactRecursiveGenerators
variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : PaperExactRecursiveGenerators R) (E : PolynomialSelfReduction R)

private theorem native_budget_mono (arguments : ℕ) {small large : ℕ} (bound : small≤large) :
    WordStack.InputBank.compileBudget arguments small≤WordStack.InputBank.compileBudget arguments large := by
  dsimp [WordStack.InputBank.compileBudget]
  gcongr

/-- All random tapes have polynomial total runtime when the filtered fibre
is nonempty. Empty fibres only need finite halting, supplied by the meter. -/
theorem filteredSource_activeTime : ∃ p : PolynomialBound,∀ n y w,y∈L→
    (R.inverseFibre n y w).Nonempty→
      (G.filteredSource E).TimeBound {input:=y,auxiliary:=w,index:=n} (p n) := by
  obtain ⟨p,budget⟩ := PaperFilteredInverse.native_polynomial_bound G.inverse E.width_computable.machine
    G.inverseSeed G.inverseTime E.width_computable.time G.labelCap
  refine ⟨p,?_⟩
  intro n y w member active bits
  obtain ⟨inputBound,labelBound⟩ := G.filteredSource_active_sizes member active
  have maximum := budget n y w bits inputBound labelBound
  by_cases enough : G.inverseSeed n≤bits.length
  · obtain ⟨word,accepted⟩ := G.filteredSource_success E member active bits enough
    obtain ⟨ticks,cost,run⟩ := PaperFilteredInverse.native_run_some G.inverse E.width_computable.machine
      G.inverseSeed G.inverseTime E.width_computable.time {input:=y,auxiliary:=w,index:=n} bits word accepted
    have smaller : ticks≤p n := cost.trans ((native_budget_mono _ (Nat.le_add_right _ _)).trans maximum)
    exact (G.filteredSource E).haltsWithin_mono _ bits smaller ⟨.accepted word,run⟩
  · obtain ⟨ticks,cost,result,run,_,_⟩ := PaperFilteredInverse.native_run G.inverse E.width_computable.machine
      G.inverseSeed G.inverseTime E.width_computable.time {input:=y,auxiliary:=w,index:=n} bits
    have extra : (if PaperFilteredInverse.commandValue G.inverse E.width_computable.machine G.inverseSeed
        G.inverseTime E.width_computable.time {input:=y,auxiliary:=w,index:=n} bits=none then bits.length else 0)≤G.inverseSeed n := by
      split_ifs <;> omega
    have smaller : ticks≤p n := cost.trans
      ((native_budget_mono _ (Nat.add_le_add_left extra _)).trans maximum)
    exact (G.filteredSource E).haltsWithin_mono _ bits smaller ⟨result,run⟩

include G E in
/-- The concrete normalization removes both strengthened legacy premises:
all-label support and uniform finite trial budgets are derived, not assumed. -/
theorem nonempty_normalized : Nonempty (ExactRecursiveGenerators R) := by
  obtain ⟨p,activeTime⟩ := G.filteredSource_activeTime E
  exact ⟨G.normalized (G.filteredSource E) p (G.filteredSource_language E)
    (fun n y w _=>G.filteredSource_noReject E n y w) activeTime⟩

end PaperExactRecursiveGenerators

/-- The current paper's exact-recursive criterion yields a legacy native
controller after a proved machine transformation, including empty alphabets. -/
theorem exactlyRecursivelyGenerable_of_paper {α : Type} [Fintype α] {L : Language α}
    (generable : PaperExactlyRecursivelyGenerable L) : ExactlyRecursivelyGenerable L := by
  obtain ⟨R,⟨E⟩,⟨G⟩⟩ := generable
  exact ⟨R,⟨E⟩,G.nonempty_normalized E⟩

theorem exactlyRecursivelyGenerable_iff_paper {α : Type} [Fintype α] (L : Language α) :
    ExactlyRecursivelyGenerable L↔PaperExactlyRecursivelyGenerable L :=
  ⟨paperExactlyRecursivelyGenerable_of_legacy,exactlyRecursivelyGenerable_of_paper⟩

/-- Proposition6.2 under exactly the current bounded-label, accepting-time
hypotheses. The native source, clocking and controller are all constructed. -/
theorem paperExactlyRecursivelyGenerable_mem_pg {α : Type} [Fintype α] {L : Language α}
    (generable : PaperExactlyRecursivelyGenerable L) : L∈PG α :=
  exactlyRecursivelyGenerable_mem_pg (exactlyRecursivelyGenerable_of_paper generable)

end
end ComplexityOfGenerators
