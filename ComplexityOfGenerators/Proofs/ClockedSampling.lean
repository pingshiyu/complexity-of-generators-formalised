import ComplexityOfGenerators.Proofs.RecognitionSearch
import ComplexityOfGenerators.Proofs.GeometricSampling

/-!
# The recognizer-to-generator sampling algorithm

Appendix A.4 uses a geometrically sampled clock and a randomly sampled word,
with a fixed language member as fallback. Here two geometric counters choose
the clock and a word's standard code. This has full support on finite words;
the definition of generability imposes no uniformity requirement on outputs.

These lemmas specify a finite-tape algorithm. The native construction in
`RecursiveGenerator` uses the same bounded candidate selection with the binary
sampler from `BinarySampling`, whose full support and almost-sure completion
are proved independently.
-/

namespace ComplexityOfGenerators

open Simulation Encodable MeasureTheory

/-- Consume true bits until the first false bit. Exhaustion is explicit. -/
def readUnary : BitString → Option (ℕ × BitString)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => (readUnary tail).map (fun p => (p.1 + 1, p.2))

theorem primrec_readUnary : Primrec readUnary := by
  have step : Primrec₂ (fun (_ : BitString) (p : Bool × BitString × Option (ℕ × BitString)) =>
      cond p.1 (p.2.2.map (fun q => (q.1 + 1, q.2))) (some (0, p.2.1))) :=
    (Primrec.cond (Primrec.fst.comp .snd)
      ((Primrec.option_map₁ ((Primrec.succ.comp .fst).pair .snd)).comp
        (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.option_some.comp ((Primrec.const 0).pair
        (Primrec.fst.comp (Primrec.snd.comp .snd))))).to₂
  exact (Primrec.list_rec .id (.const none) step).of_eq fun bits => by
    induction bits with
    | nil => rfl
    | cons bit bits ih =>
        cases bit
        · rfl
        · exact congrArg (Option.map (fun q : ℕ × BitString => (q.1 + 1, q.2))) ih

theorem readUnary_of_prefix (n : ℕ) (tail : BitString) :
    readUnary (List.replicate n true ++ false :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, readUnary, ih]

theorem readUnary_append {bits tail : BitString} {n : ℕ}
    (read : readUnary bits = some (n, tail)) (extra : BitString) :
    readUnary (bits ++ extra) = some (n, tail ++ extra) := by
  induction bits generalizing n tail with
  | nil => simp [readUnary] at read
  | cons bit bits ih =>
      cases bit with
      | false => simpa [readUnary] using read
      | true =>
          cases h : readUnary bits with
          | none => simp [readUnary, h] at read
          | some p =>
              simp only [readUnary, h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
              obtain ⟨rfl, rfl⟩ := read
              simp [readUnary, ih h]

theorem readUnary_none_iff (bits : BitString) :
    readUnary bits = none ↔ bits.count false = 0 := by
  induction bits with
  | nil => simp [readUnary]
  | cons bit bits ih => cases bit <;> simp [readUnary, ih]

theorem readUnary_splits {bits tail : BitString} {n : ℕ}
    (read : readUnary bits = some (n, tail)) :
    bits = List.replicate n true ++ false :: tail := by
  induction bits generalizing n tail with
  | nil => simp [readUnary] at read
  | cons bit bits ih =>
      cases bit with
      | false =>
          simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at read
          obtain ⟨rfl, rfl⟩ := read
          rfl
      | true =>
          cases h : readUnary bits with
          | none => simp [readUnary, h] at read
          | some p =>
              simp only [readUnary, h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
              obtain ⟨rfl, rfl⟩ := read
              rw [ih h]
              simp [List.replicate_succ]

variable {α : Type} [Primcodable α] (M : Machine α Bool Unit)

/-- A bounded simulation either returns the decoded candidate or the fallback.
The simulation runs on the empty random tape, as required by the definition of
the deterministic recognizer class. -/
def clockedCandidate (fallback : List α) (clock code : ℕ) : List α :=
  match decode (α := List α) code with
  | none => fallback
  | some word =>
      if acceptingResult M (finiteRun M (decisionData word) [] clock) then word else fallback

theorem primrec_clockedCandidate (fallback : List α) : Primrec (fun p : ℕ × ℕ =>
    clockedCandidate M fallback p.1 p.2) := by
  have run : Primrec (fun p : (ℕ × ℕ) × List α =>
      finiteRun M (decisionData p.2) [] p.1.1) :=
    (primrec_finiteRun M).comp
      (((primrec_decisionData.comp .snd).pair (.const [])).pair (Primrec.fst.comp .fst))
  have branch : Primrec₂ (fun (p : ℕ × ℕ) (word : List α) =>
      if acceptingResult M (finiteRun M (decisionData word) [] p.1) then word else fallback) := by
    have candidate := Primrec.cond ((primrec_acceptingResult M).comp run) Primrec.snd (.const fallback)
    exact candidate.to₂.of_eq fun p word => by
      cases acceptingResult M (finiteRun M (decisionData word) [] p.1) <;> rfl
  have candidate := Primrec.option_casesOn (Primrec.decode.comp .snd) (.const fallback) branch
  exact candidate.of_eq fun p => by
    unfold clockedCandidate
    cases decode (α := List α) p.2 <;> rfl

/-- Both counters must finish on the finite seed. No explicit rejection is
used when a decoded candidate is outside the language. -/
def clockedSample (fallback : List α) (bits : BitString) : Option (List α) :=
  (readUnary bits).bind fun first =>
    (readUnary first.2).map fun second => clockedCandidate M fallback first.1 second.1

theorem primrec_clockedSample (fallback : List α) : Primrec (clockedSample M fallback) := by
  have second : Primrec₂ (fun (_ : BitString) (p : ℕ × BitString) =>
      (readUnary p.2).map fun q => clockedCandidate M fallback p.1 q.1) := by
    have choose : Primrec₂ (fun (p : BitString × (ℕ × BitString)) (q : ℕ × BitString) =>
        clockedCandidate M fallback p.2.1 q.1) :=
      ((primrec_clockedCandidate M fallback).comp
        ((Primrec.fst.comp (Primrec.snd.comp .fst)).pair (Primrec.fst.comp .snd))).to₂
    exact (Primrec.option_map (primrec_readUnary.comp (Primrec.snd.comp .snd)) choose).to₂
  exact Primrec.option_bind primrec_readUnary second

theorem clockedSample_append (fallback : List α) {bits : BitString} {word : List α}
    (sample : clockedSample M fallback bits = some word) (extra : BitString) :
    clockedSample M fallback (bits ++ extra) = some word := by
  unfold clockedSample at sample ⊢
  cases first : readUnary bits with
  | none => simp [first] at sample
  | some p =>
      cases second : readUnary p.2 with
      | none => simp [first, second] at sample
      | some q =>
          rw [readUnary_append first extra]
          simp only [Option.bind_some]
          rw [readUnary_append second extra]
          simpa [first, second] using sample

theorem clockedSample_of_two_stops (fallback : List α) (bits : BitString)
    (stops : 2 ≤ bits.count false) : ∃ word, clockedSample M fallback bits = some word := by
  unfold clockedSample
  cases first : readUnary bits with
  | none =>
      have zero := (readUnary_none_iff bits).mp first
      omega
  | some p =>
      have count : bits.count false = p.2.count false + 1 := by
        rw [readUnary_splits first]
        simp [List.count_replicate]
      cases second : readUnary p.2 with
      | none =>
          have zero := (readUnary_none_iff p.2).mp second
          omega
      | some q => simp [second]

/-- Both geometric counters finish on some finite prefix almost surely, even
though the second starts at an offset determined by the first. -/
theorem clockedSample_ae_finite_prefix (fallback : List α) :
    ∀ᵐ stream ∂fairCoinMeasure, ∃ n word,
      clockedSample M fallback (streamPrefix stream n) = some word := by
  filter_upwards [fairCoin_ae_stop_after_every_offset] with stream stops
  obtain ⟨n, _, first⟩ := stops 0
  obtain ⟨m, later, second⟩ := stops (n + 1)
  let bits := streamPrefix stream (m + 1)
  have nBound : n < bits.length := by simp [bits]; omega
  have mBound : m < bits.length := by simp [bits]
  have firstBit : bits[n] = false :=
    (stream_mem_prefix_cylinder stream (m + 1) ⟨n, nBound⟩).symm.trans first
  have secondBit : bits[m] = false :=
    (stream_mem_prefix_cylinder stream (m + 1) ⟨m, mBound⟩).symm.trans second
  have member : false ∈ bits.take m := by
    apply List.mem_iff_getElem.mpr
    refine ⟨n, ?_, ?_⟩
    · simp; omega
    · simpa using firstBit
  have positive : 0 < (bits.take m).count false := List.count_pos_iff.mpr member
  have increasing := List.count_getElem_take_lt_count (xs := bits) (i := m) (hi := mBound)
  rw [secondBit] at increasing
  have two : 2 ≤ bits.count false := by omega
  obtain ⟨word, sample⟩ := clockedSample_of_two_stops M fallback bits two
  exact ⟨m + 1, word, sample⟩

def clockedSamplingEvent (fallback : List α) : Set BitStream :=
  {stream | ∃ bits word, stream ∈ cylinder bits ∧ clockedSample M fallback bits = some word}

theorem measurableSet_clockedSamplingEvent (fallback : List α) :
    MeasurableSet (clockedSamplingEvent M fallback) := by
  classical
  have description : clockedSamplingEvent M fallback =
      ⋃ bits : BitString, ⋃ (_ : (clockedSample M fallback bits).isSome), cylinder bits := by
    ext stream
    simp only [clockedSamplingEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨bits, word, member, sample⟩
      exact ⟨bits, by simp [sample], member⟩
    · rintro ⟨bits, existsWord, member⟩
      obtain ⟨word, sample⟩ := Option.isSome_iff_exists.mp existsWord
      exact ⟨bits, word, member, sample⟩
  rw [description]
  exact MeasurableSet.iUnion fun bits => MeasurableSet.iUnion fun _ => measurableSet_cylinder bits

/-- Productivity of the sampling algorithm has probability one. The native
machine compiler must preserve this event to establish `Machine.IsGenerator`. -/
theorem fairCoinMeasure_clockedSamplingEvent (fallback : List α) :
    fairCoinMeasure (clockedSamplingEvent M fallback) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_clockedSamplingEvent M fallback)).mp
  filter_upwards [clockedSample_ae_finite_prefix M fallback] with stream accepted
  obtain ⟨n, word, sample⟩ := accepted
  exact ⟨streamPrefix stream n, word, stream_mem_prefix_cylinder stream n, sample⟩

theorem clockedCandidate_sound {L : Language α} (fallback : List α)
    (fallbackMember : fallback ∈ L)
    (recognizes : ∀ word, M.Accepts (decisionData word) [] ↔ word ∈ L)
    (clock code : ℕ) : clockedCandidate M fallback clock code ∈ L := by
  unfold clockedCandidate
  cases h : decode (α := List α) code with
  | none => exact fallbackMember
  | some word =>
      simp only
      split
      · next accepted =>
          obtain ⟨output, run⟩ := (acceptingResult_correct M _).mp accepted
          exact (recognizes word).mp
            ⟨output, clock, (finiteRun_accepts_iff M (decisionData word) [] clock output).mp run⟩
      · exact fallbackMember

theorem clockedSample_sound {L : Language α} (fallback : List α)
    (fallbackMember : fallback ∈ L)
    (recognizes : ∀ word, M.Accepts (decisionData word) [] ↔ word ∈ L)
    {bits : BitString} {word : List α} (sample : clockedSample M fallback bits = some word) :
    word ∈ L := by
  unfold clockedSample at sample
  cases first : readUnary bits with
  | none => simp [first] at sample
  | some p =>
      cases second : readUnary p.2 with
      | none => simp [first, second] at sample
      | some q =>
          simp only [first, second, Option.bind_some, Option.map_some, Option.some.injEq] at sample
          rw [← sample]
          exact clockedCandidate_sound M fallback fallbackMember recognizes p.1 q.1

/-- A concrete nonempty seed for each recognized word. Extra random bits are
ignored once the clock and word code have been sampled. -/
theorem clockedSample_complete (fallback : List α) (word : List α)
    (accepted : M.Accepts (decisionData word) []) :
    ∃ bits : BitString, bits ≠ [] ∧ clockedSample M fallback bits = some word := by
  obtain ⟨output, clock, run⟩ := accepted
  let bits := List.replicate clock true ++ false ::
    (List.replicate (encode word) true ++ [false])
  refine ⟨bits, ?_, ?_⟩
  · have length : bits.length = clock + encode word + 2 := by simp [bits]; omega
    intro empty
    simp [empty] at length
  · have test : acceptingResult M (finiteRun M (decisionData word) [] clock) = true :=
      (acceptingResult_correct M _).mpr
        ⟨output, (finiteRun_accepts_iff M (decisionData word) [] clock output).mpr run⟩
    simp [clockedSample, bits, readUnary_of_prefix, clockedCandidate, test]

/-- Exact full support for the sampling algorithm, including the empty word. -/
theorem clockedSample_support {L : Language α} (fallback : List α)
    (fallbackMember : fallback ∈ L)
    (recognizes : ∀ word, M.Accepts (decisionData word) [] ↔ word ∈ L) (word : List α) :
    (∃ bits : BitString, bits ≠ [] ∧ clockedSample M fallback bits = some word) ↔ word ∈ L := by
  constructor
  · rintro ⟨bits, _, sample⟩
    exact clockedSample_sound M fallback fallbackMember recognizes sample
  · intro member
    exact clockedSample_complete M fallback word ((recognizes word).mpr member)

end ComplexityOfGenerators
