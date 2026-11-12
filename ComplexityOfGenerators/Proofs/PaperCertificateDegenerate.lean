import ComplexityOfGenerators.Proofs.PaperCertificateGeneration
import ComplexityOfGenerators.Proofs.PaperCertificateFalseChoice
import ComplexityOfGenerators.Proofs.PaperCertificateIgnoreAuxiliary
import ComplexityOfGenerators.Simulation.TranscriptVerifier
import ComplexityOfGenerators.Simulation.PolynomialClockCorrectness

/-! Certificate schemes for singleton and empty alphabets. Exactness makes
there be at most one word at each length. A fixed full false seed therefore
decides the slice; all choices and clocking are implemented by native machines.
The verifier ignores the certificate, the sampler emits source words, and the
recoverer reruns the source while ignoring its auxiliary certificate tape. -/
namespace ComplexityOfGenerators.PaperCertificates
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] [Subsingleton α]
    (G : GeneratorFamily α) (seed time : PolynomialBound)
    (bound : G.toUniformGenerators.RunsInTime seed time)

private theorem word_eq_of_length {left right : Word α} (length : left.length=right.length) : left=right := by
  apply List.ext_getElem length
  intro i leftBound rightBound
  exact Subsingleton.elim _ _

def degenerateClockedRecognizer : Machine α Bool Unit :=
  polynomialClockMachine (generatorRecognizer G.machine) (generatorRecognizerTime time)

def degenerateVerifierTime : PolynomialBound := polynomialClockTime (generatorRecognizerTime time)

def degenerateVerifierMachine : Machine α α Unit :=
  FalseChoice.machine (degenerateClockedRecognizer G time)

private theorem clocked_recognizer_bound (word : Word α) :
    (degenerateClockedRecognizer G time).TimeBound (decisionData word) (degenerateVerifierTime time word.length) :=
  polynomialClockMachine_timeBound (generatorRecognizer G.machine) (generatorRecognizerTime time) word

include bound in
theorem degenerate_verifier_accepts (word certificate : Word α) :
    (degenerateVerifierMachine G time).Accepts (verifierInput word certificate) []↔word∈G.toUniformGenerators.language := by
  let n := word.length
  let ticks := degenerateVerifierTime time n
  let size := ticks+seed n+1
  let bits := List.replicate size false
  have long : ticks<size := by dsimp [size];omega
  change (FalseChoice.machine (degenerateClockedRecognizer G time)).Accepts
    {input:=word,auxiliary:=certificate} []↔_
  rw [FalseChoice.accepts_iff _ word certificate [] size ticks long (clocked_recognizer_bound G time word)]
  constructor
  · rintro ⟨output,produced⟩
    have sourceRun := (polynomialClockMachine_produces_iff (generatorRecognizer G.machine)
      (generatorRecognizerTime time) word bits output).mp produced
    have accepted : (generatorRecognizer G.machine).Accepts (decisionData word) bits :=
      ⟨output,_,sourceRun⟩
    have original := (generatorRecognizer_accepts_iff_of_halts G.machine word bits
      ((G.isGenerator word.length).1.1 bits)).mp accepted
    exact ⟨word.length,bits,by simp [bits,size],original⟩
  · intro member
    have layer : word∈G.toUniformGenerators.layer n := by
      rw [G.layer_eq_lengthSlice];exact ⟨member,rfl⟩
    have nonempty : (G.toUniformGenerators.layer n).Nonempty := ⟨word,layer⟩
    let short := List.replicate (seed n) false
    have accepted := ((bound n).2 short (by simp [short])).mpr nonempty
    obtain ⟨output,produced⟩ := accepted
    have initialSegment : short<+:bits := by
      refine ⟨List.replicate (size-seed n) false,?_⟩
      dsimp [short,bits]
      rw [←List.replicate_add]
      congr 1
      dsimp [size]
      omega
    have produced' := G.machine.produces_prefix initialSegment produced
    have outputMember : output∈G.toUniformGenerators.layer n := ⟨bits,by simp [bits,size],produced'⟩
    have equal : output=word := word_eq_of_length (G.outputLength n output outputMember)
    rw [equal] at produced'
    have ordinary := G.machine.generatorTimeBound_timeBound_of_nonempty (generatorData n)
      (seed n) (time n) (bound n) nonempty
    have original := G.machine.produces_at_bound (generatorData n) bits (time n) word (ordinary bits) produced'
    have recognised := generatorRecognizer_accepts_at_bound G.machine time word bits original
    have bigger := (generatorRecognizerTime time).monotone (Nat.le_succ word.length)
    have padded := (generatorRecognizer G.machine).run_halted_add (decisionData word) bits
      (generatorRecognizerTime time word.length) (.accepted []) recognised
      (generatorRecognizerTime time (word.length+1)-generatorRecognizerTime time word.length)
    have atDeadline : (generatorRecognizer G.machine).run (decisionData word) bits
        (generatorRecognizerTime time (word.length+1))=.halted (.accepted []) := by
      simpa only [Nat.add_sub_of_le bigger] using padded
    exact ⟨[],(polynomialClockMachine_produces_iff (generatorRecognizer G.machine)
      (generatorRecognizerTime time) word bits []).mpr atDeadline⟩

def degenerateVerifier : PolynomialVerifier G.toUniformGenerators.language where
  machine := degenerateVerifierMachine G time
  deterministic := FalseChoice.deterministic (degenerateClockedRecognizer G time)
  time := degenerateVerifierTime time
  witnessBound := ⟨1,0,by decide⟩
  timeBound := by
    intro word certificate
    apply Machine.timeBound_mono _ _ _
      (FalseChoice.timeBound (degenerateClockedRecognizer G time) word certificate
        (degenerateVerifierTime time word.length) (clocked_recognizer_bound G time word))
    exact (degenerateVerifierTime time).monotone (by omega)
  complete := by
    intro word member
    exact ⟨[],by simp,(degenerate_verifier_accepts G seed time bound word []).mpr member⟩
  sound := fun word certificate accepted=>(degenerate_verifier_accepts G seed time bound word certificate).mp accepted

theorem degenerateVerifier_hasScheme : HasCertificateScheme (degenerateVerifier G seed time bound) := by
  refine ⟨⟨{
    sampler := G.toUniformGenerators
    time := time
    accepting_time := ?_
    covers := ?_
    certifiesInstance := ?_}⟩,⟨{
    machine := IgnoreAuxiliary.machine G.machine
    time := ⟨time.coefficient,time.degree,time.coefficient_pos⟩
    isGenerator := ?_
    recovers := ?_
    accepting_time := ?_}⟩⟩
  · intro n
    exact G.machine.generatorTimeBound_acceptingTimeBound (generatorData n) (seed n) (time n) (bound n)
  · intro n
    ext word
    constructor
    · intro member
      have layer := member
      rw [←G.layer_eq_lengthSlice] at layer
      exact ⟨member.2,word,layer,(degenerate_verifier_accepts G seed time bound word word).mpr member.1⟩
    · rintro ⟨length,certificate,_,certified⟩
      exact ⟨(degenerate_verifier_accepts G seed time bound word certificate).mp certified,length⟩
  · intro n certificate sampled
    have member := sampled
    rw [G.layer_eq_lengthSlice] at member
    exact ⟨certificate,member,(degenerate_verifier_accepts G seed time bound certificate certificate).mpr member.1⟩
  · intro n certificate
    apply IgnoreAuxiliary.generator
    simpa [IgnoreAuxiliary.data,recoveryInput,generatorData] using G.isGenerator n
  · intro n certificate
    rw [IgnoreAuxiliary.language]
    change G.toUniformGenerators.layer n=_
    rw [G.layer_eq_lengthSlice]
    ext word
    constructor
    · intro member
      exact ⟨member,(degenerate_verifier_accepts G seed time bound word certificate).mpr member.1⟩
    · exact fun member=>member.1
  · intro n certificate
    apply IgnoreAuxiliary.acceptingTimeBound
    have raw := G.machine.generatorTimeBound_acceptingTimeBound (generatorData n) (seed n) (time n) (bound n)
    apply raw.mono
    change time.coefficient*(n+1)^time.degree≤time.coefficient*(n+certificate.length+1)^time.degree
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem pg_has_degenerate_certificateScheme {L : Language α} (member : L∈PG α) :
    ∃ V : PolynomialVerifier L,HasCertificateScheme V := by
  obtain ⟨G,language,seed,time,bound⟩ := member
  subst L
  exact ⟨degenerateVerifier G seed time bound,degenerateVerifier_hasScheme G seed time bound⟩

end
end ComplexityOfGenerators.PaperCertificates
