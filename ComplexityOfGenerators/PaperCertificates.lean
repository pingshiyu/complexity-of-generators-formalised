import ComplexityOfGenerators.Certificates
import ComplexityOfGenerators.Proofs.ResourceGeneration

/-! The current paper's certificate interface. Certificates use the instance
alphabet, include the empty word, and all certificate obligations are total.
Generator costs constrain accepting runs only. Historical binary-positive
certificate schemes remain in `Certificates.lean` under their original names. -/
namespace ComplexityOfGenerators.PaperCertificates

variable {α : Type} [Fintype α] (L : Language α)

def verifierInput (word certificate : Word α) : InputData α α :=
  {input:=word,auxiliary:=certificate}

def recoveryInput (n : ℕ) (certificate : Word α) : InputData Unit α :=
  {index:=n,auxiliary:=certificate}

structure PolynomialVerifier where
  machine : Machine α α Unit
  deterministic : machine.Deterministic
  time : PolynomialBound
  witnessBound : PolynomialBound
  timeBound : ∀ word certificate,machine.TimeBound (verifierInput word certificate)
    (time (word.length+certificate.length+1))
  complete : ∀ word,word∈L→∃ certificate : Word α,
    certificate.length≤witnessBound word.length ∧ machine.Accepts (verifierInput word certificate) []
  sound : ∀ word certificate,machine.Accepts (verifierInput word certificate) []→word∈L

namespace PolynomialVerifier
variable {L}
def certifiedInputs (V : PolynomialVerifier L) (certificate : Word α) : Language α :=
  {word | V.machine.Accepts (verifierInput word certificate) []}

omit [Fintype α] in
theorem certifiedInputs_subset (V : PolynomialVerifier L) (certificate : Word α) :
    V.certifiedInputs certificate⊆L := fun _ certified=>V.sound _ _ certified
end PolynomialVerifier

variable {L}
structure CertificateGenerator (V : PolynomialVerifier L) where
  sampler : UniformGenerators α
  time : PolynomialBound
  accepting_time : ∀ n,sampler.machine.AcceptingTimeBound (generatorData n) (time n)
  covers : ∀ n,lengthSlice L n=
    {word | word.length=n ∧ ∃ certificate,certificate∈sampler.layer n ∧ word∈V.certifiedInputs certificate}
  certifiesInstance : ∀ n certificate,certificate∈sampler.layer n→
    (lengthSlice L n∩V.certifiedInputs certificate).Nonempty

structure CertificateRecoverer (V : PolynomialVerifier L) where
  machine : Machine Unit α α
  time : BivariatePolynomialBound
  isGenerator : ∀ n certificate,machine.IsGenerator (recoveryInput n certificate)
  recovers : ∀ n certificate,machine.generatedLanguage (recoveryInput n certificate)=
    lengthSlice L n∩V.certifiedInputs certificate
  accepting_time : ∀ n certificate,machine.AcceptingTimeBound (recoveryInput n certificate)
    (time n certificate.length)

def HasCertificateScheme (V : PolynomialVerifier L) : Prop :=
  Nonempty (CertificateGenerator V) ∧ Nonempty (CertificateRecoverer V)

/-- Empty instance slices force the sampler to have empty support. -/
theorem CertificateGenerator.empty_of_empty {V : PolynomialVerifier L}
    (S : CertificateGenerator V) (n : ℕ) (empty : lengthSlice L n=∅) : S.sampler.layer n=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro certificate sampled
  obtain ⟨word,member,_⟩ := S.certifiesInstance n certificate sampled
  rw [empty] at member
  exact member

end ComplexityOfGenerators.PaperCertificates
