import ComplexityOfGenerators.Simulation.ComputableEvaluator
import ComplexityOfGenerators.Simulation.RecursivePrograms
import Mathlib.Computability.RE

/-!
# Searching for a finite accepting seed

The generator-to-recognizer direction of Theorem 3.1 searches over pairs of
nonempty finite seeds and clocks. The bounded test is primitive recursive by
the verified native evaluator. Mathlib's unbounded search then gives a
partial-recursive recognizer with exactly the generated language as its domain.
No halting or productivity assumption is needed for this direction.
-/

namespace ComplexityOfGenerators

open Simulation Encodable

variable {I A O : Type} [Primcodable I] [Primcodable A] [Primcodable O]
variable (M : Machine I A O)

/-- Equality is tested on the standard natural-number encodings, so the test
does not require an additional computational assumption about output symbols. -/
def boundedOutputTest (data : InputData I A) (word : List O) (bits : BitString) (clock : ℕ) : Bool :=
  encode (finiteRun M data bits clock) == encode (Sum.inr (Sum.inl word) : FiniteResult M)

omit [Primcodable I] [Primcodable A] in
theorem boundedOutputTest_correct (data : InputData I A) (word : List O)
    (bits : BitString) (clock : ℕ) :
    boundedOutputTest M data word bits clock = true ↔
      M.run data bits clock = .halted (.accepted word) := by
  rw [boundedOutputTest, beq_iff_eq, encode_injective.eq_iff, finiteRun_accepts_iff]

theorem primrec_boundedOutputTest : Primrec (fun p : (InputData I A × List O) × (BitString × ℕ) =>
    boundedOutputTest M p.1.1 p.1.2 p.2.1 p.2.2) := by
  have run : Primrec (fun p : (InputData I A × List O) × (BitString × ℕ) =>
      finiteRun M p.1.1 p.2.1 p.2.2) := (primrec_finiteRun M).comp
    (((Primrec.fst.comp .fst).pair (Primrec.fst.comp .snd)).pair (Primrec.snd.comp .snd))
  exact Primrec.beq.comp (Primrec.encode.comp run)
    (Primrec.encode.comp (Primrec.sumInr.comp (Primrec.sumInl.comp (Primrec.snd.comp .fst))))

/-- One search index encodes both a finite random tape and a simulation clock.
Invalid codes and empty tapes fail the test, exactly as in `generatedLanguage`. -/
def seedTest (data : InputData I A) (word : List O) (index : ℕ) : Bool :=
  (decode (α := BitString × ℕ) index).casesOn false
    (fun witness => !(witness.1.length == 0) && boundedOutputTest M data word witness.1 witness.2)

theorem primrec_seedTest : Primrec (fun p : (InputData I A × List O) × ℕ =>
    seedTest M p.1.1 p.1.2 p.2) := by
  have branch : Primrec₂ (fun (p : (InputData I A × List O) × ℕ) (w : BitString × ℕ) =>
      !(w.1.length == 0) && boundedOutputTest M p.1.1 p.1.2 w.1 w.2) := by
    exact (Primrec.and.comp
      (Primrec.not.comp (Primrec.beq.comp
        (Primrec.list_length.comp (Primrec.fst.comp .snd)) (.const 0)))
      ((primrec_boundedOutputTest M).comp ((Primrec.fst.comp .fst).pair .snd))).to₂
  exact Primrec.option_casesOn (Primrec.decode.comp .snd) (.const false) branch

omit [Primcodable I] [Primcodable A] in
theorem seedTest_correct (data : InputData I A) (word : List O) (index : ℕ) :
    seedTest M data word index = true ↔
      ∃ bits clock, decode index = some (bits, clock) ∧ bits ≠ [] ∧
        M.run data bits clock = .halted (.accepted word) := by
  unfold seedTest
  cases h : decode (α := BitString × ℕ) index with
  | none => simp
  | some witness =>
      rcases witness with ⟨bits, clock⟩
      simp [boundedOutputTest_correct, List.length_eq_zero_iff]

/-- Dovetail over seeds and clocks: a nonhalting run on one seed never blocks
the tests of subsequent seeds. -/
def seedSearch (data : InputData I A) (word : List O) : Part ℕ :=
  Nat.rfind (fun index => Part.some (seedTest M data word index))

theorem partrec_seedSearch : Partrec (fun p : InputData I A × List O => seedSearch M p.1 p.2) :=
  Partrec.rfind (primrec_seedTest M).to_comp.partrec.to₂

set_option backward.isDefEq.respectTransparency false in
omit [Primcodable I] [Primcodable A] in
/-- The enumerator's domain is exactly the paper's finite-seed output support,
including its convention that the seed must be nonempty. -/
theorem seedSearch_dom_iff (data : InputData I A) (word : List O) :
    (seedSearch M data word).Dom ↔ word ∈ M.generatedLanguage data := by
  have search : (seedSearch M data word).Dom ↔ ∃ index, seedTest M data word index = true := by
    unfold seedSearch
    rw [Nat.rfind_dom]
    constructor
    · rintro ⟨index, test, _⟩
      exact ⟨index, (Part.mem_some_iff.mp test).symm⟩
    · rintro ⟨index, test⟩
      exact ⟨index, Part.mem_some_iff.mpr test.symm, fun {_} _ => trivial⟩
  rw [search]
  constructor
  · rintro ⟨index, test⟩
    obtain ⟨bits, clock, _, nonempty, accepts⟩ := (seedTest_correct M data word index).mp test
    exact ⟨bits, nonempty, clock, accepts⟩
  · rintro ⟨bits, nonempty, clock, accepts⟩
    refine ⟨encode (bits, clock), (seedTest_correct M data word _).mpr ?_⟩
    exact ⟨bits, clock, encodek _, nonempty, accepts⟩

/-- Generator support is recursively enumerable in Mathlib's sense, for every
native machine. A separate native input adapter is needed to conclude membership
in the paper's class `RE` on the original word alphabet. -/
theorem generatedLanguage_rePred (data : InputData I A) : REPred (fun word => word ∈ M.generatedLanguage data) :=
  ((partrec_seedSearch M).comp ((Computable.const data).pair Computable.id)).dom_re.of_eq
    (fun word => seedSearch_dom_iff M data word)

/-- The natural-number interface used by the library's recursive-code compiler.
Malformed word codes diverge rather than creating spurious accepted words. -/
def encodedSeedSearch (data : InputData I A) (code : ℕ) : Part ℕ :=
  (decode (α := List O) code : Part (List O)).bind (seedSearch M data)

theorem partrec_encodedSeedSearch (data : InputData I A) : Partrec (encodedSeedSearch M data) :=
  (@Computable.decode (List O) _).ofOption.bind
    (((partrec_seedSearch M).comp ((Computable.const data).pair Computable.snd)).to₂)

/-- A concrete finite-control recognizer obtained by composing the seed search
with the verified recursive-program compiler. The input encoding is explicit;
`GenerabilityContainment` composes this with the original-alphabet adapter.
-/
theorem native_encoded_support_recognizer (data : InputData I A) :
    ∃ native : Machine RecursiveAlphabet Bool Unit, native.Deterministic ∧
      ∀ word bits, native.Accepts (decisionData (recursiveInput [encode word])) bits ↔
        word ∈ M.generatedLanguage data := by
  obtain ⟨native, deterministic, accepts⟩ :=
    native_recognizer_of_partrec (partrec_encodedSeedSearch M data)
  refine ⟨native, deterministic, ?_⟩
  intro word bits
  rw [accepts]
  simpa [encodedSeedSearch] using seedSearch_dom_iff M data word

end ComplexityOfGenerators
