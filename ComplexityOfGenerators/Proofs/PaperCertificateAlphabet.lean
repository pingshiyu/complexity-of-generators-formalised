import ComplexityOfGenerators.Proofs.PaperCertificateGeneration
import ComplexityOfGenerators.Proofs.PolynomialCertificateSchemes
import ComplexityOfGenerators.Foundations.SymbolRelabel

/-! Certificate schemes over the instance alphabet. A two-letter retract
encodes binary step transcripts without changing their length. Every other
certificate is interpreted by the total letter decoder, including the empty
certificate; no positivity or validity restriction enters the new interface. -/
namespace ComplexityOfGenerators.PaperCertificates
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G : GeneratorFamily α)
    (encode : Bool→α) (decode : α→Bool)
    (retract : ∀ bit,decode (encode bit)=bit)
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time)

include retract in
theorem decode_encode (certificate : BitString) : (certificate.map encode).map decode=certificate := by
  induction certificate with
  | nil => rfl
  | cons bit tail ih => simp only [List.map_cons,retract,ih]

def verifierMachine : Machine α α Unit :=
  SymbolRelabel.machine (transcriptVerifierMachine G.machine) id decode id

theorem verifier_accepts (word certificate : Word α) :
    (verifierMachine G decode).Accepts (verifierInput word certificate) []↔
      (transcriptVerifierMachine G.machine).Accepts (verifierData word (certificate.map decode)) [] := by
  simpa [verifierMachine,SymbolRelabel.data,verifierInput,verifierData] using
    SymbolRelabel.accepts (transcriptVerifierMachine G.machine) id decode id (verifierInput word certificate) []

def alphabetTranscriptVerifier : PolynomialVerifier G.toUniformGenerators.language where
  machine := verifierMachine G decode
  deterministic := SymbolRelabel.deterministic (transcriptVerifierMachine G.machine) id decode id
    (transcriptVerifierMachine_deterministic G.machine)
  time := transcriptVerifierTime
  witnessBound := time.add ⟨1,0,by decide⟩
  timeBound := by
    intro word certificate
    apply SymbolRelabel.timeBound
    simpa [SymbolRelabel.data,verifierInput,verifierData] using
      transcriptVerifierMachine_timeBound G.machine word (certificate.map decode)
  complete := by
    intro word member
    have layer : word∈G.toUniformGenerators.layer word.length := by
      rw [G.layer_eq_lengthSlice];exact ⟨member,rfl⟩
    obtain ⟨certificate,_,length,recovered⟩ := transcriptRecoverer_bounded_complete G seed time bound word.length word layer
    refine ⟨certificate.map encode,?_,?_⟩
    · simp only [List.length_map]
      exact length.trans (by simpa [PolynomialBound.eval] using time.add_le ⟨1,0,by decide⟩ word.length)
    · rw [verifier_accepts,decode_encode encode decode retract]
      apply (transcriptVerifierMachine_accepts G.machine word certificate).mpr
      rw [transcriptRecoverer_language] at recovered
      exact recovered
  sound := by
    intro word certificate accepted
    have source := (verifier_accepts G decode word certificate).mp accepted
    have replay := (transcriptVerifierMachine_accepts G.machine word (certificate.map decode)).mp source
    have recovered : word∈(transcriptRecoverer G.machine).generatedLanguage
        (generatorData word.length (certificate.map decode)) := by
      rw [transcriptRecoverer_language];exact replay
    exact ⟨word.length,transcriptRecoverer_language_subset G word.length _ recovered⟩

def recovererMachine : Machine Unit α α :=
  SymbolRelabel.machine (transcriptRecoverer G.machine) id decode id

theorem recoverer_language (n : ℕ) (certificate : Word α) :
    (recovererMachine G decode).generatedLanguage (recoveryInput n certificate)=
      (transcriptRecoverer G.machine).generatedLanguage (generatorData n (certificate.map decode)) := by
  simpa [recovererMachine,SymbolRelabel.data,recoveryInput,generatorData] using
    SymbolRelabel.language (transcriptRecoverer G.machine) id decode id (recoveryInput n certificate)

theorem recovery_certified (n : ℕ) (certificate : Word α) :
    (recovererMachine G decode).generatedLanguage (recoveryInput n certificate)=
      lengthSlice G.toUniformGenerators.language n∩
        (alphabetTranscriptVerifier G encode decode retract seed time bound).certifiedInputs certificate := by
  rw [recoverer_language]
  ext word
  constructor
  · intro recovered
    have member := transcriptRecoverer_language_subset G n (certificate.map decode) recovered
    have length := G.outputLength n word member
    refine ⟨?_,?_⟩
    · rwa [G.layer_eq_lengthSlice] at member
    · apply (verifier_accepts G decode word certificate).mpr
      apply (transcriptVerifierMachine_accepts G.machine word (certificate.map decode)).mpr
      rw [transcriptRecoverer_language] at recovered
      change (transcriptReplay G.machine).run (generatorData n (certificate.map decode)) []
        (certificate.map decode).length=.halted (.accepted word) at recovered
      simpa only [length] using recovered
  · rintro ⟨member,certified⟩
    have source := (verifier_accepts G decode word certificate).mp certified
    have replay := (transcriptVerifierMachine_accepts G.machine word (certificate.map decode)).mp source
    rw [transcriptRecoverer_language]
    change (transcriptReplay G.machine).run (generatorData n (certificate.map decode)) []
      (certificate.map decode).length=.halted (.accepted word)
    simpa only [member.2] using replay

def alphabetSampler : UniformGenerators α where
  machine := SymbolRelabel.machine (transcriptSampler G.machine) id id encode
  isGenerator := by
    intro n
    apply SymbolRelabel.generator
    simpa [SymbolRelabel.data,generatorData,transcriptUniformSampler] using
      (transcriptUniformSampler G.toUniformGenerators).isGenerator n

theorem sampler_layer (n : ℕ) : (alphabetSampler G encode).layer n=
    List.map encode '' (transcriptUniformSampler G.toUniformGenerators).layer n := by
  simpa [alphabetSampler,SymbolRelabel.data,generatorData,transcriptUniformSampler,UniformGenerators.layer] using
    SymbolRelabel.language (transcriptSampler G.machine) id id encode (generatorData n)

theorem alphabetTranscriptVerifier_hasScheme :
    HasCertificateScheme (alphabetTranscriptVerifier G encode decode retract seed time bound) := by
  obtain ⟨q,accepting⟩ := (transcriptUniformSampler_polynomial G.toUniformGenerators ⟨seed,time,bound⟩).acceptingPolynomialTime
  refine ⟨⟨{
    sampler := alphabetSampler G encode
    time := q
    accepting_time := ?_
    covers := ?_
    certifiesInstance := ?_}⟩,⟨{
    machine := recovererMachine G decode
    time := ⟨1,1,by decide⟩
    isGenerator := ?_
    recovers := recovery_certified G encode decode retract seed time bound
    accepting_time := ?_}⟩⟩
  · intro n
    apply SymbolRelabel.acceptingTimeBound
    simpa [SymbolRelabel.data,generatorData,transcriptUniformSampler] using accepting n
  · intro n
    ext word
    constructor
    · intro member
      have layer := member
      rw [←G.layer_eq_lengthSlice] at layer
      obtain ⟨certificate,sampled,recovered⟩ := transcriptSampler_covers G n word layer
      have sampled' : certificate.map encode∈(alphabetSampler G encode).layer n := by
        rw [sampler_layer];exact ⟨certificate,sampled,rfl⟩
      have recovered' : word∈(recovererMachine G decode).generatedLanguage (recoveryInput n (certificate.map encode)) := by
        rw [recoverer_language,decode_encode encode decode retract]
        exact recovered
      rw [recovery_certified G encode decode retract seed time bound] at recovered'
      exact ⟨member.2,certificate.map encode,sampled',recovered'.2⟩
    · rintro ⟨length,certificate,_,certified⟩
      exact ⟨(alphabetTranscriptVerifier G encode decode retract seed time bound).sound word certificate certified,length⟩
  · intro n certificate sampled
    rw [sampler_layer] at sampled
    obtain ⟨source,sampled,rfl⟩ := sampled
    obtain ⟨_,word,_,recovered⟩ := transcriptSampler_recovers_instance G n source sampled
    have recovered' : word∈(recovererMachine G decode).generatedLanguage (recoveryInput n (source.map encode)) := by
      rw [recoverer_language,decode_encode encode decode retract]
      exact recovered
    rw [recovery_certified G encode decode retract seed time bound] at recovered'
    exact ⟨word,recovered'⟩
  · intro n certificate
    apply SymbolRelabel.generator
    simpa [SymbolRelabel.data,recoveryInput,generatorData] using
      transcriptRecoverer_isGenerator G.machine n (certificate.map decode)
  · intro n certificate
    apply SymbolRelabel.acceptingTimeBound
    have raw := (transcriptRecoverer G.machine).generatorTimeBound_acceptingTimeBound
      (generatorData n (certificate.map decode)) 1 ((certificate.map decode).length+1)
      (transcriptRecoverer_trialBound G.machine n (certificate.map decode))
    apply raw.mono
    simp only [List.length_map,BivariatePolynomialBound.eval,pow_one,one_mul]
    omega

theorem pg_has_alphabet_certificateScheme {L : Language α} (member : L∈PG α)
    (encode : Bool→α) (decode : α→Bool) (retract : ∀ bit,decode (encode bit)=bit) :
    ∃ V : PolynomialVerifier L,HasCertificateScheme V := by
  obtain ⟨G,language,seed,time,bound⟩ := member
  subst L
  exact ⟨alphabetTranscriptVerifier G encode decode retract seed time bound,
    alphabetTranscriptVerifier_hasScheme G encode decode retract seed time bound⟩

theorem certificate_equivalence_of_nontrivial [Nontrivial α] (L : Language α) :
    L∈PG α↔∃ V : PolynomialVerifier L,HasCertificateScheme V := by
  classical
  constructor
  · intro member
    obtain ⟨zero,one,different⟩ := exists_pair_ne α
    let encode : Bool→α := fun bit=>if bit then one else zero
    let decode : α→Bool := fun value=>decide (value=one)
    have retract : ∀ bit,decode (encode bit)=bit := by
      intro bit
      cases bit <;> simp [encode,decode,different]
    exact pg_has_alphabet_certificateScheme member encode decode retract
  · rintro ⟨V,scheme⟩
    exact hasCertificateScheme_mem_pg scheme

end
end ComplexityOfGenerators.PaperCertificates
