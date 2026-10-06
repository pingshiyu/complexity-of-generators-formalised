import ComplexityOfGenerators.ComplexityClasses

/-!
# Collision resistance (Definitions 5.3–5.4)

The hash family is unkeyed and its attacks are uniform. A hash at security
parameter `n` maps `n+1` bits to `n` bits. The typed lengths below follow Definition
5.3, avoiding the inconsistent hash index in Definition 5.5's collision language.
The main separation theorem does not depend on a chosen pair encoding.
-/

namespace ComplexityOfGenerators

open scoped ENNReal

abbrev Bits (n : ℕ) := Fin n → Bool

def bitsWord {n : ℕ} (x : Bits n) : BitString := List.ofFn x

/-- Definition 5.3, including one uniform polynomial-time implementation. -/
structure HashFunction where
  hash : (n : ℕ) → Bits (n + 1) → Bits n
  implementation : Machine Bool Bool Bool
  deterministic : implementation.Deterministic
  time : PolynomialBound
  computes : ∀ n x,
    implementation.Produces { input := bitsWord x, index := n } [] (bitsWord (hash n x))
  timeBound : ∀ n (x : Bits (n + 1)),
    implementation.TimeBound { input := bitsWord x, index := n } (time n)

/-- At parameter `n`, a genuine collision has two distinct `n+1`-bit preimages. -/
def HashFunction.IsCollision (h : HashFunction) (n : ℕ) (x y : BitString) : Prop :=
  ∃ a b : Bits (n + 1), x = bitsWord a ∧ y = bitsWord b ∧ a ≠ b ∧ h.hash n a = h.hash n b

/-- A reserved output separator for collision-finding algorithms. -/
inductive PairSymbol where
  | bit (b : Bool)
  | separator
  deriving DecidableEq, Fintype

def encodePair (x y : BitString) : List PairSymbol :=
  x.map PairSymbol.bit ++ [PairSymbol.separator] ++ y.map PairSymbol.bit

/-- Uniform randomised polynomial-time algorithms. These are general algorithms,
not generators: they may explicitly fail or output an unsuccessful candidate. -/
structure CollisionFinder where
  machine : Machine Unit Bool PairSymbol
  time : PolynomialBound
  bounded : ∀ n, machine.TimeBound (generatorData n) (time n)

/-- The success event on fair independent random bits. Failure and divergence do
not count as success, and the collision condition checks the preimage lengths. -/
def collisionSuccess (h : HashFunction) (A : CollisionFinder) (n : ℕ) : Set BitStream :=
  { stream | ∃ x y b,
      stream ∈ cylinder b ∧
      A.machine.Produces (generatorData n) b (encodePair x y) ∧
      h.IsCollision n x y }

/-- Definition 5.4: no uniform polynomial attack has inverse-polynomial success
for infinitely many security parameters. `Set.Infinite` expresses that quantifier
literally, and the probability threshold uses the paper's strict inequality. -/
def HashFunction.CollisionResistant (h : HashFunction) : Prop :=
  ¬ ∃ A : CollisionFinder, ∃ q : PolynomialBound,
    Set.Infinite { n : ℕ |
      (q n : ℝ≥0∞)⁻¹ < fairCoinMeasure (collisionSuccess h A n) }

def CollisionResistantHashFunctionsExist : Prop :=
  ∃ h : HashFunction, h.CollisionResistant

end ComplexityOfGenerators
