import ComplexityOfGenerators.Proofs.SeedEnumeration

/-! A second use of the verified bounded evaluator: enumerating clocks on a
fixed input and random tape. This connects native recognizers to Mathlib's
partial-recursive predicates without assuming a machine-model equivalence. -/

namespace ComplexityOfGenerators

open Simulation

variable {I A O : Type} [Primcodable I] [Primcodable A] [Primcodable O]
variable (M : Machine I A O)

def acceptingResult : FiniteResult M → Bool :=
  fun r => Sum.casesOn r (fun _ => false)
    (fun halted => Sum.casesOn halted (fun _ => true) (fun _ => false))

omit [Primcodable I] [Primcodable A] in
theorem primrec_acceptingResult : Primrec (acceptingResult M) := by
  have halted : Primrec₂ (fun (_ : FiniteResult M) (r : List O ⊕ Bool) =>
      Sum.casesOn (motive := fun _ => Bool) r (fun _ => true) (fun _ => false)) :=
    Primrec.sumCasesOn .snd (Primrec.const true).to₂ (Primrec.const false).to₂
  exact Primrec.sumCasesOn .id (Primrec.const false).to₂ halted

omit [Primcodable I] [Primcodable A] [Primcodable O] in
theorem acceptingResult_correct (result : FiniteResult M) :
    acceptingResult M result = true ↔ ∃ word, result = Sum.inr (Sum.inl word) := by
  cases result with
  | inl c => simp [acceptingResult]
  | inr halted => cases halted <;> simp [acceptingResult]

def acceptanceSearch (data : InputData I A) (bits : BitString) : Part ℕ :=
  Nat.rfind (fun clock => Part.some (acceptingResult M (finiteRun M data bits clock)))

theorem partrec_acceptanceSearch : Partrec (fun p : InputData I A × BitString =>
    acceptanceSearch M p.1 p.2) :=
  Partrec.rfind ((primrec_acceptingResult M).comp (primrec_finiteRun M)).to_comp.partrec.to₂

set_option backward.isDefEq.respectTransparency false in
omit [Primcodable I] [Primcodable A] [Primcodable O] in
theorem acceptanceSearch_dom_iff (data : InputData I A) (bits : BitString) :
    (acceptanceSearch M data bits).Dom ↔ M.Accepts data bits := by
  unfold acceptanceSearch
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨clock, accepts, _⟩
    have test := (Part.mem_some_iff.mp accepts).symm
    obtain ⟨word, output⟩ := (acceptingResult_correct M _).mp test
    exact ⟨word, clock, (finiteRun_accepts_iff M data bits clock word).mp output⟩
  · rintro ⟨word, clock, accepts⟩
    have test := (acceptingResult_correct M _).mpr
      ⟨word, (finiteRun_accepts_iff M data bits clock word).mpr accepts⟩
    exact ⟨clock, Part.mem_some_iff.mpr test.symm, fun {_} _ => trivial⟩

theorem native_acceptance_rePred (bits : BitString) :
    REPred (fun data : InputData I A => M.Accepts data bits) :=
  ((partrec_acceptanceSearch M).comp (Computable.id.pair (Computable.const bits))).dom_re.of_eq
    (fun data => acceptanceSearch_dom_iff M data bits)

variable {α : Type} [Fintype α] [Primcodable α]

omit [Fintype α] in
/-- Every recognizer in the paper's native class gives a recursively enumerable
predicate in Mathlib. This implication needs neither totality nor a resource bound. -/
theorem native_RE_rePred {L : Language α} (member : L ∈ RE α) :
    REPred (fun word => word ∈ L) := by
  obtain ⟨native, _deterministic, accepts⟩ := member
  have data : Primrec (fun word : List α => decisionData word) :=
    (Primrec.of_equiv_symm (e := inputDataEquiv)).comp
      (Primrec.id.pair ((Primrec.const []).pair (Primrec.const 0)))
  have recursive := (partrec_acceptanceSearch native).comp
    (data.to_comp.pair (Computable.const []))
  exact recursive.dom_re.of_eq fun word =>
    (acceptanceSearch_dom_iff native (decisionData word) []).trans (accepts word)

omit [Fintype α] in
/-- Every native generator's language gives a recursively enumerable predicate
in Mathlib. `GenerabilityContainment` supplies the native input-encoding adapter. -/
theorem native_GEN_rePred {L : Language α} (member : L ∈ GEN α) :
    REPred (fun word => word ∈ L) := by
  obtain ⟨native, _generator, language⟩ := member
  exact (generatedLanguage_rePred native (generatorData 0)).of_eq
    (fun word => by rw [language])

end ComplexityOfGenerators
