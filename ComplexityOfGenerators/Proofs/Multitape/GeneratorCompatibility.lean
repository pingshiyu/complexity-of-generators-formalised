import ComplexityOfGenerators.Proofs.Multitape.PolynomialCompatibility
import ComplexityOfGenerators.Proofs.UpToPolynomialGeneration

/-! Polynomial up-to generation is unchanged by moving between the native
machine and the actual finite bank model. Arbitrary time is not preserved by
the quadratic compiler; every polynomial overhead used below is explicit. -/

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

/-- Compile only accepting executions; unsuccessful source executions need not
satisfy any time bound. Finite-source termination is used only for semantic
reflection, not charged as a bounded simulation. -/
theorem acceptingTimeBound_toNative (M : MultitapeMachine Unit Bool α)
    (data : InputData Unit Bool) (terminates : M.Terminates data)
    (time : ℕ) (bounded : M.AcceptingTimeBound data time) :
    M.toNative.AcceptingTimeBound data (1 + (time + 1) * (2 * time + 4)) := by
  intro bits word produced
  obtain ⟨ticks, execution⟩ := (M.produces_toNative_iff data terminates bits word).mp produced
  have small := bounded bits ticks word execution
  obtain ⟨nativeTicks, cost, run⟩ := M.executes_toNative data bits ticks (.accepted word) execution
  have large : nativeTicks ≤ 1 + (time + 1) * (2 * time + 4) := by
    apply cost.trans
    exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.add_le_add_right small 1)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 small) 4)) 1
  have later := M.toNative.run_halted_add data bits nativeTicks (.accepted word) run
    (1 + (time + 1) * (2 * time + 4) - nativeTicks)
  simpa only [Nat.add_sub_of_le large] using later

def UniformGenerators.toNative (G : UniformGenerators α) :
    ComplexityOfGenerators.UniformGenerators α where
  machine := G.machine.toNative
  isGenerator := fun n => G.machine.isGenerator_toNative _ (G.isGenerator n)

theorem UniformGenerators.toNative_layer (G : UniformGenerators α) (n : ℕ) :
    G.toNative.layer n = G.layer n :=
  G.machine.generatedLanguage_toNative _ (G.isGenerator n).1.1

def ofNativeUniform (G : ComplexityOfGenerators.UniformGenerators α) : UniformGenerators α where
  machine := Simulation.TransducerBank.Native.machine G.machine
  isGenerator := fun n => Simulation.TransducerBank.Native.isGenerator G.machine _ (G.isGenerator n)

theorem ofNativeUniform_layer (G : ComplexityOfGenerators.UniformGenerators α) (n : ℕ) :
    (ofNativeUniform G).layer n = G.layer n :=
  Simulation.TransducerBank.Native.generatedLanguage G.machine _ (G.isGenerator n).1.1

theorem ofNativeUniform_language (G : ComplexityOfGenerators.UniformGenerators α) :
    (ofNativeUniform G).language = G.language := by
  ext word
  exact exists_congr fun n => Set.ext_iff.mp (ofNativeUniform_layer G n) word

def UpToGeneratorFamily.toNative (G : UpToGeneratorFamily α) :
    ComplexityOfGenerators.UpToGeneratorFamily α G.toUniformGenerators.language where
  toUniformGenerators := G.toUniformGenerators.toNative
  layers := fun n => by
    rw [UniformGenerators.toNative_layer]
    exact G.prefixLanguage n

theorem nativeUpTo_language (language : Language α)
    (G : ComplexityOfGenerators.UpToGeneratorFamily α language) :
    G.toUniformGenerators.language = language := by
  ext word
  change (∃ n, word ∈ G.toUniformGenerators.layer n) ↔ word ∈ language
  constructor
  · rintro ⟨n, member⟩
    rw [G.layers] at member
    exact member.1
  · intro member
    exact ⟨word.length, by rw [G.layers]; exact ⟨member, Nat.le_refl _⟩⟩

def ofNativeUpTo (language : Language α)
    (G : ComplexityOfGenerators.UpToGeneratorFamily α language) : UpToGeneratorFamily α where
  toUniformGenerators := ofNativeUniform G.toUniformGenerators
  prefixLanguage := fun n => by
    rw [ofNativeUniform_layer, ofNativeUniform_language, nativeUpTo_language language G]
    exact G.layers n

/-- The polynomial accepting-time specialisation of the actual bank up-to class. -/
def PGUpTo (α : Type) [Fintype α] : LanguageClass α :=
  {language | ∃ G : UpToGeneratorFamily α,
    G.toUniformGenerators.language = language ∧ ∃ time : PolynomialBound,
      ∀ n, G.machine.AcceptingTimeBound (generatorData n) (time n)}

theorem pgUpTo_eq_native_pgUpTo : PGUpTo α = ComplexityOfGenerators.PGUpTo α := by
  ext language
  constructor
  · rintro ⟨G, same, time, bounded⟩
    subst language
    refine ⟨G.toNative, compiledPolynomialTime time, ?_⟩
    intro n bits word produced
    have run := acceptingTimeBound_toNative G.machine (generatorData n)
      (G.isGenerator n).1.1 (time n) (bounded n) bits word produced
    have cost := compiledPolynomialTime_bound time n
    have later := G.machine.toNative.run_halted_add (generatorData n) bits
      (1 + (time n + 1) * (2 * time n + 4)) (.accepted word) run
      (compiledPolynomialTime time n - (1 + (time n + 1) * (2 * time n + 4)))
    change G.machine.toNative.run (generatorData n) bits (compiledPolynomialTime time n) =
      .halted (.accepted word)
    simpa only [Nat.add_sub_of_le cost] using later
  · rintro ⟨G, time, bounded⟩
    refine ⟨ofNativeUpTo language G, ?_, time, ?_⟩
    · rw [show (ofNativeUpTo language G).toUniformGenerators =
        ofNativeUniform G.toUniformGenerators from rfl, ofNativeUniform_language,
        nativeUpTo_language language G]
    · intro n
      exact Simulation.TransducerBank.Native.acceptingTimeBound G.machine (generatorData n)
        (G.isGenerator n).1.1 (time n) (bounded n)

/-- Both sides have concrete native implementations; this is the polynomial
specialisation, not the still separate arbitrary-resource characterisation. -/
theorem pgUpTo_eq_np : PGUpTo α = NP α := by
  rw [pgUpTo_eq_native_pgUpTo, ComplexityOfGenerators.pgUpTo_eq_np, np_eq_native_np]

end
end ComplexityOfGenerators.Multitape
