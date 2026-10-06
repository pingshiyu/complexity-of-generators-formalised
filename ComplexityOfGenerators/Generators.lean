import ComplexityOfGenerators.Machine
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

/-! # Generators (Definitions 2.3–2.9, 3.1, and 4.1–4.2) -/

namespace ComplexityOfGenerators

open MeasureTheory

/-- Definition 2.6: independent unbiased coin flips, not an arbitrary measure. -/
noncomputable def fairCoinMeasure : Measure BitStream :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- Definition 2.7: the cylinder consisting of extensions of a finite bitstring. -/
def cylinder (b : BitString) : Set BitStream :=
  { stream | ∀ i : Fin b.length, stream i = b[i] }

namespace Machine

variable {I A O : Type} (M : Machine I A O)

/-- Definition 2.3: finite runs halt, and the only rejection is input exhaustion.
The latter is built into `next`; this predicate excludes explicit rejections. -/
def HaltingTransducer (data : InputData I A) : Prop :=
  (∀ b, M.Halts data b) ∧
  (∀ b t, M.run data b t ≠ .halted .rejected)

/-- Definitions 2.5 and 2.8: a stream is accepted if an accepted finite prefix exists.
For read-once transducers this is the same union as the minimal-prefix definition. -/
def acceptedStreams (data : InputData I A) : Set BitStream :=
  { stream | ∃ b, stream ∈ cylinder b ∧ M.Accepts data b }

/-- Definition 2.9: almost-sure productivity, or the empty-generator case. -/
def IsGenerator (data : InputData I A) : Prop :=
  M.HaltingTransducer data ∧
  (fairCoinMeasure (M.acceptedStreams data) = 1 ∨
    fairCoinMeasure (M.acceptedStreams data) = 0)

/-- Definition 3.1: exactly the outputs produced from nonempty finite random tapes.
In particular, there is no lower bound on the probability of any individual word. -/
def generatedLanguage (data : InputData I A) : Language O :=
  { w | ∃ b, b ≠ [] ∧ M.Produces data b w }

end Machine

variable (α : Type) [Fintype α]

/-- Definition 3.2: all languages of genuine generators, including the empty one. -/
def GEN : LanguageClass α :=
  { L | ∃ M : Machine Unit Bool α,
      M.IsGenerator (generatorData 0) ∧ M.generatedLanguage (generatorData 0) = L }

/-- Definition 4.1: uniformity is enforced by using one finite machine for all indices.
The index is a read-only unary tape, not nonuniform advice. This structure does not
yet restrict the lengths of the outputs (certificate generators also use it). -/
structure UniformGenerators where
  machine : Machine Unit Bool α
  isGenerator : ∀ n, machine.IsGenerator (generatorData n)

namespace UniformGenerators

variable {α}

def layer (G : UniformGenerators α) (n : ℕ) : Language α :=
  G.machine.generatedLanguage (generatorData n)

def language (G : UniformGenerators α) : Language α :=
  { w | ∃ n, w ∈ G.layer n }

end UniformGenerators

/-- Definition 4.2, length partition: the `n`-th generator produces only length `n`. -/
structure GeneratorFamily extends UniformGenerators α where
  outputLength : ∀ n w, w ∈ toUniformGenerators.layer n → w.length = n

/-- The length-`n` part of a language, including length zero. -/
def lengthSlice {α : Type} (L : Language α) (n : ℕ) : Language α :=
  { w | w ∈ L ∧ w.length = n }

end ComplexityOfGenerators
