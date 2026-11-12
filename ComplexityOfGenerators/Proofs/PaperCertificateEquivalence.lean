import ComplexityOfGenerators.Proofs.PaperCertificateAlphabet
import ComplexityOfGenerators.Proofs.PaperCertificateDegenerate

/-! Proposition 6.1 for every finite alphabet, with the current paper's
certificate alphabet, empty certificates, all-certificate support obligations
and accepting-only runtime bounds. -/
namespace ComplexityOfGenerators.PaperCertificates

theorem certificate_equivalence {α : Type} [Fintype α] (L : Language α) :
    L∈PG α↔∃ V : PolynomialVerifier L,HasCertificateScheme V := by
  cases subsingleton_or_nontrivial α with
  | inl trivial =>
      letI := trivial
      constructor
      · exact pg_has_degenerate_certificateScheme
      · rintro ⟨V,scheme⟩
        exact hasCertificateScheme_mem_pg scheme
  | inr nontrivial =>
      letI := nontrivial
      exact certificate_equivalence_of_nontrivial L

end ComplexityOfGenerators.PaperCertificates
