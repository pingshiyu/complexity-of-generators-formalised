import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Components

/-! The finite dynamic program used by the native Kleene-star generator.
Entries remain in increasing length order and are never overwritten. -/
namespace ComplexityOfGenerators.Simulation.StarGenerator

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

abbrev Table (α : Type) := List (Option (List α))

def next (seed time : PolynomialBound) (table : Table α) (m j : ℕ)
    (p : Option (List α) × BitString) : Option (List α) × BitString :=
  let source := UnionGenerator.sourceValue G time j (p.2.take (seed j))
  let previous := (table[m - j]?).bind id
  let tail := p.2.drop (seed j)
  (ConcatenationGenerator.offer p.1 (ConcatenationGenerator.pairValue source previous)
      (tail.head? == some true), tail.drop 1)

def stage (seed time : PolynomialBound) (table : Table α) (m : ℕ)
    (bits : BitString) : Option (List α) × BitString :=
  (List.range' 1 m).foldl (fun p j => next G seed time table m j p) (none, bits)

def extend (seed time : PolynomialBound) (m : ℕ) (p : Table α × BitString) : Table α × BitString :=
  let answer := stage G seed time p.1 m p.2
  (p.1 ++ [answer.1], answer.2)

def tableRun (seed time : PolynomialBound) (n : ℕ) (bits : BitString) : Table α × BitString :=
  (List.range' 1 n).foldl (fun p m => extend G seed time m p) ([some []], bits)

def algorithm (seed time : PolynomialBound) (n : ℕ) (bits : BitString) : Option (List α) :=
  ((tableRun G seed time n bits).1.getLast?).bind id

end ComplexityOfGenerators.Simulation.StarGenerator
