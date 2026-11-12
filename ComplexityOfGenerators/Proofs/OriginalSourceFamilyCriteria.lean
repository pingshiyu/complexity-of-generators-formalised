import ComplexityOfGenerators.Proofs.OriginalSourceClosureSupport

/-! Package bounds obtained from actual direct-call executions. The criteria
require real native run equations and introduce no abstract compiler premise. -/
namespace ComplexityOfGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

namespace UniformGenerators

theorem union_activeIndices_infinite (R G H : UniformGenerators α)
    (layers : ∀ n,R.layer n=IndexedSupport.unionLayers G.layer H.layer n)
    (active : G.activeIndices.Infinite) : R.activeIndices.Infinite := by
  have result := IndexedSupport.union_active_infinite G.layer H.layer active
  apply result.mono
  intro n member
  change (R.layer n).Nonempty
  rwa [layers]

theorem concat_activeIndices_infinite (R G H : UniformGenerators α)
    (layers : ∀ n,R.layer n=IndexedSupport.concatLayers G.layer H.layer n)
    (active : G.activeIndices.Infinite) (j : ℕ) (right : (H.layer j).Nonempty) :
    R.activeIndices.Infinite := by
  have result := IndexedSupport.concat_active_infinite G.layer H.layer active j right
  apply result.mono
  intro n member
  change (R.layer n).Nonempty
  rwa [layers]

theorem star_activeIndices_infinite (R G : UniformGenerators α)
    (layers : ∀ n,R.layer n=IndexedSupport.starLayers G.layer n)
    (active : G.activeIndices.Infinite) : R.activeIndices.Infinite := by
  have result := IndexedSupport.star_active_infinite G.layer active
  apply result.mono
  intro n member
  change (R.layer n).Nonempty
  rwa [layers]

end UniformGenerators

namespace OriginalSourceClosure

def wordClock (outer call target source : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (outer.asPolynomial.comp target.asPolynomial+
    (call.asPolynomial.comp target.asPolynomial)*source.asPolynomial)

theorem wordClock_lower (outer call target source : PolynomialBound) (n m : ℕ)
    (index : n≤target m) : outer n+call n*source m≤wordClock outer call target source m := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ m)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,PolynomialBound.asPolynomial_eval]
  exact Nat.add_le_add (outer.monotone index) (Nat.mul_le_mul_right _ (call.monotone index))

/-- A real lucky run with polynomial source work and a polynomial producing
index yields the current global word-length fast-path property. -/
theorem globalWordPolynomialTime_of_call_paths (G : UniformGenerators α)
    (outer call target source : PolynomialBound)
    (paths : ∀ word∈G.language,∃ n bits ticks,bits≠[] ∧ n≤target word.length ∧
      ticks≤outer n+call n*source word.length ∧
      G.machine.run (generatorData n) bits ticks=.halted (.accepted word)) : G.GlobalWordPolynomialTime := by
  refine ⟨wordClock outer call target source,?_⟩
  intro word member
  obtain ⟨n,bits,ticks,nonempty,index,bound,run⟩ := paths word member
  have deadline := bound.trans (wordClock_lower outer call target source n word.length index)
  refine ⟨n,bits,nonempty,?_⟩
  have padded := G.machine.run_halted_add (generatorData n) bits ticks (.accepted word) run
    (wordClock outer call target source word.length-ticks)
  rwa [Nat.add_sub_of_le deadline] at padded

end OriginalSourceClosure
end
end ComplexityOfGenerators
