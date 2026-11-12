import ComplexityOfGenerators.PaperSelfReducibility
import ComplexityOfGenerators.Proofs.PaperCertificateBounds
import ComplexityOfGenerators.Proofs.ExactRecursiveSupport

/-!
# Deriving inverse trial budgets from accepting-time bounds

A bounded call may be made on an arbitrary label. Its result is retained only
when its length is at most the target and the supplied label has the computed
width of that result. Any retained result therefore puts the original call
inside the paper's promised label domain. This removes the need to compute the
bound, or to make assumptions about inverse machines outside that domain.
-/
namespace ComplexityOfGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Machine
variable {I A O : Type} (M : Machine I A O)

/-- Accepting-time bounds give one fixed seed length supporting every output,
without a halting-time bound on empty members. -/
theorem accepting_full_seed_witness (data : InputData I A) (time seed : ℕ)
    (long : time < seed) (bounded : M.AcceptingTimeBound data time) (word : Word O) :
    word ∈ M.generatedLanguage data ↔
      ∃ bits : BitString, bits.length = seed ∧ M.run data bits time = .halted (.accepted word) := by
  constructor
  · rintro ⟨bits,nonempty,produced⟩
    have accepted := bounded bits word produced
    let padded := bits ++ List.replicate seed false
    let fixed := padded.take seed
    have paddedLength : seed ≤ padded.length := by simp [padded]
    have fixedLength : fixed.length=seed := by simp [fixed,Nat.min_eq_left paddedLength]
    have paddedRun : M.run data padded time=.halted (.accepted word) := by
      simpa only [padded] using M.run_append_of_not_exhausted data bits (List.replicate seed false) time
        (by simp [accepted]) |>.trans accepted
    have extend := M.run_append_of_not_exhausted data fixed (padded.drop seed) time
      (M.run_not_exhausted_of_length data fixed time (by omega))
    have same : fixed ++ padded.drop seed=padded := List.take_append_drop seed padded
    rw [same,paddedRun] at extend
    exact ⟨fixed,fixedLength,extend.symm⟩
  · rintro ⟨bits,length,accepted⟩
    refine ⟨bits,?_,time,accepted⟩
    intro empty
    simp [empty] at length
    omega

end Machine

namespace PaperExactRecursiveGenerators
variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : PaperExactRecursiveGenerators R)

def inverseSeed : PolynomialBound := AcceptingTimeGeneration.seed G.inverseTime

theorem inverseSeed_long (n : ℕ) : G.inverseTime n < G.inverseSeed n := by
  have bound := AcceptingTimeGeneration.seed_lower G.inverseTime n
  change G.inverseTime n<AcceptingTimeGeneration.seed G.inverseTime n
  omega

/-- Semantic value of the actual bounded-call and width-filter construction. -/
def filteredTrial (n : ℕ) (y w : Word α) (bits : BitString) : Option (Word α) :=
  match G.inverse.run { input := y, auxiliary := w, index := n } bits (G.inverseTime n) with
  | .halted (.accepted x) => if x.length≤n ∧ w.length=R.width x then some x else none
  | _ => none

theorem filteredTrial_eq_some (n : ℕ) (y w x : Word α) (bits : BitString) :
    G.filteredTrial n y w bits=some x ↔
      G.inverse.run { input := y, auxiliary := w, index := n } bits (G.inverseTime n)=.halted (.accepted x) ∧
      x.length≤n ∧ w.length=R.width x := by
  unfold filteredTrial
  cases run : G.inverse.run { input := y, auxiliary := w, index := n } bits (G.inverseTime n) with
  | running c => simp
  | halted result =>
      cases result with
      | rejected => simp
      | exhausted => simp
      | accepted value =>
          change (if value.length≤n ∧ w.length=R.width value then some value else none)=some x ↔ _
          by_cases valid : value.length≤n ∧ w.length=R.width value
          · simp only [ite_eq_left valid,Option.some.injEq]
            constructor
            · intro equal; subst x; exact ⟨rfl,valid⟩
            · rintro ⟨equal,other⟩; exact Outcome.accepted.inj (RunState.halted.inj equal)
          · rw [ite_eq_right valid]
            constructor
            · intro impossible;cases impossible
            · rintro ⟨equal,size,width⟩
              have same := Outcome.accepted.inj (RunState.halted.inj equal)
              subst x
              exact False.elim (valid ⟨size,width⟩)

theorem filteredTrial_sound {n : ℕ} {y w x : Word α} (member : y∈L)
    {bits : BitString} (output : G.filteredTrial n y w bits=some x) : x∈R.inverseFibre n y w := by
  obtain ⟨run,size,width⟩ := (G.filteredTrial_eq_some n y w x bits).mp output
  have label : w.length≤G.labelBound n := width ▸ G.width_le n x size
  rw [←G.inverse_language n y w member label]
  exact (G.inverse.mem_generatedLanguage_iff_produces _ x).mpr ⟨bits,G.inverseTime n,run⟩

/-- Retained candidates force the label into the promised domain, even
when the source is arbitrary outside that domain. -/
theorem filteredTrial_label_bound {n : ℕ} {y w x : Word α} {bits : BitString}
    (output : G.filteredTrial n y w bits=some x) : w.length≤G.labelBound n := by
  obtain ⟨run,size,width⟩ := (G.filteredTrial_eq_some n y w x bits).mp output
  calc
    w.length=R.width x := width
    _≤G.labelBound n := G.width_le n x size

def labelCap : PolynomialBound := ⟨G.logCoefficient+G.logConstant+1,1,by omega⟩

theorem filteredTrial_label_cap {n : ℕ} {y w x : Word α} {bits : BitString}
    (output : G.filteredTrial n y w bits=some x) : w.length≤G.labelCap n := by
  have log := Nat.log_le_self 2 (n+1)
  have bound := (G.filteredTrial_label_bound output).trans (G.labelBound_log n)
  change w.length≤(G.logCoefficient+G.logConstant+1)*(n+1)^1
  rw [pow_one]
  nlinarith

theorem filteredTrial_none_of_label_long {n : ℕ} {y w : Word α}
    (long : G.labelBound n<w.length) (bits : BitString) : G.filteredTrial n y w bits=none := by
  cases result : G.filteredTrial n y w bits with
  | none => rfl
  | some x => have bound := G.filteredTrial_label_bound result;omega

theorem filteredTrial_input_length {n : ℕ} {y w x : Word α} (member : y∈L)
    {bits : BitString} (output : G.filteredTrial n y w bits=some x) : y.length≤n := by
  have target := G.filteredTrial_sound member output
  have reduced := R.length_reduce x w
  rw [target.2.1] at reduced
  have length := R.ancestor_length_le target.1
  omega

theorem filteredTrial_none_of_input_long {n : ℕ} {y w : Word α} (member : y∈L)
    (long : n<y.length) (bits : BitString) : G.filteredTrial n y w bits=none := by
  cases result : G.filteredTrial n y w bits with
  | none => rfl
  | some x => have bound := G.filteredTrial_input_length member result;omega

theorem filteredTrial_complete {n : ℕ} {y w x : Word α} (member : y∈L)
    (target : x∈R.inverseFibre n y w) :
    ∃ bits : BitString,bits.length=G.inverseSeed n ∧ G.filteredTrial n y w bits=some x := by
  have size := R.ancestor_length_le target.1
  have label : w.length≤G.labelBound n := target.2.2 ▸ G.width_le n x size
  have source : x∈G.inverse.generatedLanguage { input := y, auxiliary := w, index := n } := by
    rwa [G.inverse_language n y w member label]
  obtain ⟨bits,length,run⟩ := (G.inverse.accepting_full_seed_witness _ (G.inverseTime n)
    (G.inverseSeed n) (G.inverseSeed_long n) (G.inverse_time n y w member label) x).mp source
  exact ⟨bits,length,(G.filteredTrial_eq_some n y w x bits).mpr ⟨run,size,target.2.2⟩⟩

/-- Every full trial succeeds on nonempty fibres, including on exceptional
random tapes. Empty fibres have no successful trial. -/
theorem filteredTrial_success_iff {n : ℕ} {y w : Word α} (member : y∈L)
    (bits : BitString) (length : bits.length=G.inverseSeed n) :
    (∃ x,G.filteredTrial n y w bits=some x) ↔ (R.inverseFibre n y w).Nonempty := by
  constructor
  · rintro ⟨x,output⟩;exact ⟨x,G.filteredTrial_sound member output⟩
  · rintro ⟨x,target⟩
    have size := R.ancestor_length_le target.1
    have label : w.length≤G.labelBound n := target.2.2 ▸ G.width_le n x size
    have active : (G.inverse.generatedLanguage { input := y, auxiliary := w, index := n }).Nonempty := by
      rw [G.inverse_language n y w member label];exact ⟨x,target⟩
    have bound := G.inverse_time n y w member label
    obtain ⟨z,produced⟩ := G.inverse.accepts_long_tape_of_acceptingTimeBound _ (G.inverseTime n)
      (G.inverse_generator n y w member label) bound bits (by have := G.inverseSeed_long n;omega) active
    have inFibre : z∈R.inverseFibre n y w := by
      rw [←G.inverse_language n y w member label]
      exact (G.inverse.mem_generatedLanguage_iff_produces _ z).mpr ⟨bits,produced⟩
    exact ⟨z,(G.filteredTrial_eq_some n y w z bits).mpr
      ⟨bound bits z produced,R.ancestor_length_le inFibre.1,inFibre.2.2⟩⟩

/-- No unbounded call or trial budget is introduced in the base normalization. -/
def normalizedBase : UniformGenerators α where
  machine := AcceptingTimeGeneration.machine G.base G.baseTime
  isGenerator := AcceptingTimeGeneration.isGenerator G.base G.baseTime G.base_time

theorem normalizedBase_language (n : ℕ) : (G.normalizedBase).layer n=R.bases n := by
  change (AcceptingTimeGeneration.machine G.base G.baseTime).generatedLanguage (generatorData n)=_
  rw [AcceptingTimeGeneration.generatedLanguage G.base G.baseTime G.base_time,G.base_language]

theorem normalizedBase_polynomialTime : G.normalizedBase.PolynomialTime :=
  ⟨AcceptingTimeGeneration.seed G.baseTime,AcceptingTimeGeneration.time G.baseTime,
    AcceptingTimeGeneration.trialBound G.base G.baseTime G.base_time⟩

end PaperExactRecursiveGenerators
end
end ComplexityOfGenerators
