import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Semantics

/-! The actual native filtered source has the all-label inverse fibres needed
by the existing exact-recursive controller. Its source assumptions are exactly
the paper's bounded-label, accepting-time clauses. -/
namespace ComplexityOfGenerators.PaperExactRecursiveGenerators
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : PaperExactRecursiveGenerators R) (E : PolynomialSelfReduction R)

private theorem widthMachine_correct (x : Word α) :
    E.width_computable.machine.Produces {input:=x} [] (List.replicate (R.width x) ()) := by
  simpa using E.width_computable.computes x []

private theorem widthMachine_bounded (x : Word α) :
    E.width_computable.machine.TimeBound {input:=x} (E.width_computable.time x.length) := by
  simpa using E.width_computable.timeBound x []

def filteredSource : Machine α α α :=
  PaperFilteredInverse.machine G.inverse E.width_computable.machine G.inverseSeed G.inverseTime E.width_computable.time

theorem filteredSource_value_iff (n : ℕ) (y w x : Word α) (bits : BitString) :
    PaperFilteredInverse.commandValue G.inverse E.width_computable.machine G.inverseSeed G.inverseTime
      E.width_computable.time {input:=y,auxiliary:=w,index:=n} bits=some x↔
      G.inverseSeed n≤bits.length ∧ G.filteredTrial n y w (bits.take (G.inverseSeed n))=some x := by
  by_cases enough : G.inverseSeed n≤bits.length
  · simp only [PaperFilteredInverse.commandValue,enough,ite_true,true_and]
    exact (PaperFilteredInverse.body_accept_iff G.inverse E.width_computable.machine G.inverseSeed G.inverseTime
      E.width_computable.time R.width (widthMachine_correct E) (widthMachine_bounded E)
      {input:=y,auxiliary:=w,index:=n} bits x).trans
      (G.filteredTrial_eq_some n y w x (bits.take (G.inverseSeed n))).symm
  · simp [PaperFilteredInverse.commandValue,enough]

theorem filteredSource_produces_iff (n : ℕ) (y w x : Word α) (bits : BitString) :
    (G.filteredSource E).Produces {input:=y,auxiliary:=w,index:=n} bits x↔
      G.inverseSeed n≤bits.length ∧ G.filteredTrial n y w (bits.take (G.inverseSeed n))=some x := by
  change (PaperFilteredInverse.machine G.inverse E.width_computable.machine G.inverseSeed G.inverseTime
    E.width_computable.time).Produces _ bits x↔_
  rw [PaperFilteredInverse.machine_produces_iff]
  exact G.filteredSource_value_iff E n y w x bits

theorem filteredSource_language (n : ℕ) (y w : Word α) (member : y∈L) :
    (G.filteredSource E).generatedLanguage {input:=y,auxiliary:=w,index:=n}=R.inverseFibre n y w := by
  ext x
  constructor
  · rintro ⟨bits,_,produced⟩
    exact G.filteredTrial_sound member ((G.filteredSource_produces_iff E n y w x bits).mp produced).2
  · intro target
    obtain ⟨bits,length,hit⟩ := G.filteredTrial_complete member target
    have nonempty : bits≠[] := by
      have positive := G.inverseSeed.positive n
      intro empty
      simp [empty] at length
      omega
    have fixed : bits.take (G.inverseSeed n)=bits := by rw [←length,List.take_length]
    refine ⟨bits,nonempty,(G.filteredSource_produces_iff E n y w x bits).mpr ⟨by omega,?_⟩⟩
    simpa only [fixed] using hit

theorem filteredSource_halting (n : ℕ) (y w : Word α) :
    (G.filteredSource E).HaltingTransducer {input:=y,auxiliary:=w,index:=n} :=
  PaperFilteredInverse.machine_halting G.inverse E.width_computable.machine G.inverseSeed G.inverseTime
    E.width_computable.time _

theorem filteredSource_noReject (n : ℕ) (y w : Word α) (bits : BitString) (ticks : ℕ) :
    (G.filteredSource E).run {input:=y,auxiliary:=w,index:=n} bits ticks≠.halted .rejected :=
  (G.filteredSource_halting E n y w).2 bits ticks

theorem filteredSource_success {n : ℕ} {y w : Word α} (member : y∈L)
    (active : (R.inverseFibre n y w).Nonempty) (bits : BitString) (enough : G.inverseSeed n≤bits.length) :
    ∃ x,PaperFilteredInverse.commandValue G.inverse E.width_computable.machine G.inverseSeed G.inverseTime
      E.width_computable.time {input:=y,auxiliary:=w,index:=n} bits=some x := by
  have length : (bits.take (G.inverseSeed n)).length=G.inverseSeed n := by simp [List.length_take,Nat.min_eq_left enough]
  obtain ⟨x,hit⟩ := (G.filteredTrial_success_iff member (bits.take (G.inverseSeed n)) length).mpr active
  exact ⟨x,(G.filteredSource_value_iff E n y w x bits).mpr ⟨enough,hit⟩⟩

theorem filteredSource_active_sizes {n : ℕ} {y w : Word α} (member : y∈L)
    (active : (R.inverseFibre n y w).Nonempty) : y.length≤n ∧ w.length≤G.labelCap n := by
  obtain ⟨x,target⟩ := active
  obtain ⟨bits,_,hit⟩ := G.filteredTrial_complete member target
  exact ⟨G.filteredTrial_input_length member hit,G.filteredTrial_label_cap hit⟩

end
end ComplexityOfGenerators.PaperExactRecursiveGenerators
