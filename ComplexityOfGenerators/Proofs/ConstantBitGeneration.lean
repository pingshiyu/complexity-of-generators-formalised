import ComplexityOfGenerators.Proofs.ReplayGenerators
import ComplexityOfGenerators.Foundations.LanguageClosure

/-!
# The disjoint fallback languages in the intersection argument

The size-`n` machine emits `n` copies of the selected bit. At size zero it
rejects, which the verified drain compiler converts to exhaustion. Both
languages therefore belong to native `PG`, with seed budget one and runtime
`n+1`. Their disjointness includes the empty-word boundary.
-/

namespace ComplexityOfGenerators

open Simulation

set_option backward.isDefEq.respectTransparency false

def positiveWordEmitter (bit : Bool) : Machine Unit Bool Bool where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 2
  symbols := 0
  initial := 0
  transition := fun q _ _ index _ => match index with
    | some _ => .step 1 none .stay .stay .stay .right (some bit)
    | none => if q = 0 then .reject else .accept

def positiveWordConfiguration (bit : Bool) (k : ℕ) : Configuration (positiveWordEmitter bit) :=
  {(positiveWordEmitter bit).initialConfiguration with
    state := if k = 0 then (0 : Fin 2) else (1 : Fin 2)
    indexHead := k
    output := List.replicate k bit}

theorem positiveWordEmitter_deterministic (bit : Bool) : (positiveWordEmitter bit).Deterministic := by
  intro q input auxiliary index work
  cases index <;> simp [positiveWordEmitter]
  split_ifs <;> trivial

theorem positiveWordEmitter_run (bit : Bool) (n : ℕ) (bits : BitString) (k : ℕ) (bound : k ≤ n) :
    (positiveWordEmitter bit).run (generatorData n) bits k =
      (positiveWordEmitter bit).observe (generatorData n) bits (positiveWordConfiguration bit k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have available : k < n := by omega
      rw [Machine.run, ih (by omega)]
      simp [Machine.observe, Machine.next, positiveWordEmitter, positiveWordConfiguration,
        Machine.initialConfiguration, generatorData, available, Move.onInput, Move.onInt,
        List.replicate_succ']

def positiveWordOutcome (bit : Bool) (n : ℕ) : Outcome Bool :=
  if n = 0 then .rejected else .accepted (List.replicate n bit)

theorem positiveWordEmitter_halts (bit : Bool) (n : ℕ) (bits : BitString) :
    (positiveWordEmitter bit).run (generatorData n) bits n = .halted (positiveWordOutcome bit n) := by
  rw [positiveWordEmitter_run bit n bits n le_rfl]
  by_cases zero : n = 0
  · simp [Machine.observe, positiveWordEmitter, positiveWordConfiguration, Machine.initialConfiguration,
      generatorData, positiveWordOutcome, zero]
  · simp [Machine.observe, positiveWordEmitter, positiveWordConfiguration, Machine.initialConfiguration,
      generatorData, positiveWordOutcome, zero]

noncomputable def constantBitGenerator (bit : Bool) : Machine Unit Bool Bool :=
  rejectDrain (positiveWordEmitter bit)

theorem constantBitGenerator_language (bit : Bool) (n : ℕ) :
    (constantBitGenerator bit).generatedLanguage (generatorData n) =
      if n = 0 then ∅ else {List.replicate n bit} := by
  by_cases zero : n = 0
  · have source : (positiveWordEmitter bit).run (generatorData n) [] n = .halted .rejected := by
      simpa [positiveWordOutcome, zero] using positiveWordEmitter_halts bit n []
    simpa [constantBitGenerator, zero] using
      rejectDrain_language (positiveWordEmitter bit) (positiveWordEmitter_deterministic bit)
        (generatorData n) n .rejected source
  · have source : (positiveWordEmitter bit).run (generatorData n) [] n =
        .halted (.accepted (List.replicate n bit)) := by
      simpa [positiveWordOutcome, zero] using positiveWordEmitter_halts bit n []
    simpa [constantBitGenerator, zero] using
      rejectDrain_language (positiveWordEmitter bit) (positiveWordEmitter_deterministic bit)
        (generatorData n) n (.accepted (List.replicate n bit)) source

theorem constantBitGenerator_isGenerator (bit : Bool) (n : ℕ) :
    (constantBitGenerator bit).IsGenerator (generatorData n) :=
  rejectDrain_isGenerator (positiveWordEmitter bit) (positiveWordEmitter_deterministic bit)
    _ n (positiveWordOutcome bit n) (positiveWordEmitter_halts bit n [])

theorem constantBitGenerator_trialBound (bit : Bool) (n : ℕ) :
    (constantBitGenerator bit).GeneratorTimeBound (generatorData n) 1 (n + 1) :=
  rejectDrain_trialBound (positiveWordEmitter bit) (positiveWordEmitter_deterministic bit)
    _ n (positiveWordOutcome bit n) (positiveWordEmitter_halts bit n []) 1

theorem constantBitLanguage_in_pg (bit : Bool) : constantBitLanguage bit ∈ PG Bool := by
  let G : GeneratorFamily Bool := {
    machine := constantBitGenerator bit
    isGenerator := constantBitGenerator_isGenerator bit
    outputLength := by
      intro n word member
      change word ∈ (constantBitGenerator bit).generatedLanguage (generatorData n) at member
      rw [constantBitGenerator_language] at member
      split_ifs at member with zero
      · exact False.elim member
      · have equal : word = List.replicate n bit := member
        simp [equal] }
  refine ⟨G, ?_, ⟨1, 0, by decide⟩, ⟨1, 1, by decide⟩, ?_⟩
  · ext word
    change (∃ n, word ∈ (constantBitGenerator bit).generatedLanguage (generatorData n)) ↔
      word ≠ [] ∧ ∀ letter ∈ word, letter = bit
    simp only [constantBitGenerator_language]
    constructor
    · rintro ⟨n, member⟩
      split_ifs at member with zero
      · exact False.elim member
      · have equal : word = List.replicate n bit := member
        subst word
        exact ⟨by simpa using zero, fun letter member => (List.mem_replicate.mp member).2⟩
    · rintro ⟨nonempty, letters⟩
      refine ⟨word.length, ?_⟩
      rw [ite_eq_right (by simpa using nonempty)]
      exact List.eq_replicate_iff.mpr ⟨rfl, letters⟩
  · intro n
    simpa [PolynomialBound.eval] using constantBitGenerator_trialBound bit n

end ComplexityOfGenerators
