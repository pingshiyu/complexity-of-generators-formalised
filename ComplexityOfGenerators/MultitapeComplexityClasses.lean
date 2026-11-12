import ComplexityOfGenerators.MultitapeSpace
import ComplexityOfGenerators.ComplexityClasses

/-!
# Explicit multitape classes for the general resource characterisations

These classes refer to the actual finite bank model in `MultitapeModel`.
The native classes with the same mathematical role remain unchanged. In
particular, a bank transition and a quadratic single-work-tape simulation are
not assigned the same time cost.

`ResourceOrder f g` is the usual eventual multiplicative bound on natural
functions. A separate total resource function makes the treatment of finitely
many small inputs explicit; it does not add a constant to the paper's bound.
-/

namespace ComplexityOfGenerators.Multitape

/-- `f(n)=O(g(n))`, with all constants and the finite initial segment explicit. -/
def ResourceOrder (f g : ℕ → ℕ) : Prop :=
  ∃ constant threshold : ℕ, 0 < constant ∧
    ∀ n, threshold ≤ n → f n ≤ constant * g n

theorem ResourceOrder.refl (f : ℕ → ℕ) : ResourceOrder f f :=
  ⟨1, 0, by decide, fun _ _ => by simp⟩

theorem ResourceOrder.trans {f g h : ℕ → ℕ}
    (first : ResourceOrder f g) (second : ResourceOrder g h) : ResourceOrder f h := by
  obtain ⟨a, startA, positiveA, boundA⟩ := first
  obtain ⟨b, startB, positiveB, boundB⟩ := second
  refine ⟨a * b, max startA startB, Nat.mul_pos positiveA positiveB, ?_⟩
  intro n large
  calc
    f n ≤ a * g n := boundA n ((Nat.le_max_left _ _).trans large)
    _ ≤ a * (b * h n) := Nat.mul_le_mul_left a
      (boundB n ((Nat.le_max_right _ _).trans large))
    _ = (a * b) * h n := (Nat.mul_assoc _ _ _).symm

variable (α : Type) [Fintype α]

/-- Ordinary-input nondeterministic time on a fixed finite work-tape bank. -/
def NTIME (time : ℕ → ℕ) : LanguageClass α :=
  {language | ∃ M : MultitapeMachine α Bool Unit, ∃ runtime : ℕ → ℕ,
    ResourceOrder runtime time ∧
    (∀ word, M.TimeBound (decisionData word) (runtime word.length)) ∧
    ∀ word, (∃ bits, M.Accepts (decisionData word) bits) ↔ word ∈ language}

/-- Ordinary-input nondeterministic space. Every input has a finite bound on
all choice branches; no resource bound is imposed on that running time. -/
def NSPACE (space : ℕ → ℕ) : LanguageClass α :=
  {language | ∃ M : MultitapeMachine α Bool Unit, ∃ workspace : ℕ → ℕ,
    ResourceOrder workspace space ∧
    (∀ word, ∃ time, M.TimeBound (decisionData word) time) ∧
    (∀ word, M.CellSpaceBound (decisionData word) (workspace word.length)) ∧
    ∀ word, (∃ bits, M.Accepts (decisionData word) bits) ↔ word ∈ language}

/-- A uniform probabilistic family on the genuine finite bank model. -/
structure UniformGenerators where
  machine : MultitapeMachine Unit Bool α
  isGenerator : ∀ n, machine.IsGenerator (generatorData n)

namespace UniformGenerators

variable {α}

def layer (G : UniformGenerators α) (n : ℕ) : Language α :=
  G.machine.generatedLanguage (generatorData n)

def language (G : UniformGenerators α) : Language α :=
  {word | ∃ n, word ∈ G.layer n}

end UniformGenerators

/-- Exact length in every nonempty layer. -/
structure GeneratorFamily extends UniformGenerators α where
  outputLength : ∀ n word, word ∈ toUniformGenerators.layer n → word.length = n

/-- Exact generators with the paper's bound on accepting executions only. -/
def GTIME (time : ℕ → ℕ) : LanguageClass α :=
  {language | ∃ G : GeneratorFamily α,
    G.toUniformGenerators.language = language ∧
    ∀ n, G.machine.AcceptingTimeBound (generatorData n) (time n)}

/-- Exact generators bounded in work space. -/
def GSPACE (space : ℕ → ℕ) : LanguageClass α :=
  {language | ∃ G : GeneratorFamily α,
    G.toUniformGenerators.language = language ∧
    ∀ n, G.machine.CellSpaceBound (generatorData n) (space n)}

/-- Up-to generators: the entire prefix of the language is available at size n. -/
structure UpToGeneratorFamily extends UniformGenerators α where
  prefixLanguage : ∀ n,
    toUniformGenerators.layer n =
      {word | word ∈ toUniformGenerators.language ∧ word.length ≤ n}

/-- The multitape up-to time class; every accepting branch has O(time(n)) steps. -/
def GTIMEUpTo (time : ℕ → ℕ) : LanguageClass α :=
  {language | ∃ G : UpToGeneratorFamily α, ∃ runtime : ℕ → ℕ,
    G.toUniformGenerators.language = language ∧
    ResourceOrder runtime time ∧
    ∀ n, G.machine.AcceptingTimeBound (generatorData n) (runtime n)}

/-- The multitape up-to space class. -/
def GSPACEUpTo (space : ℕ → ℕ) : LanguageClass α :=
  {language | ∃ G : UpToGeneratorFamily α, ∃ workspace : ℕ → ℕ,
    G.toUniformGenerators.language = language ∧
    ResourceOrder workspace space ∧
    ∀ n, G.machine.CellSpaceBound (generatorData n) (workspace n)}

end ComplexityOfGenerators.Multitape
