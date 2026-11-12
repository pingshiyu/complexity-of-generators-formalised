import ComplexityOfGenerators.ComplexityClasses

/-! First-success semantics for repeated, equally sized random blocks. -/
namespace ComplexityOfGenerators.Simulation.FixedBlockRetry

variable {O : Type}

def scan (width : ℕ) (phase : BitString → Option (List O)) : ℕ → BitString → Option (List O)
  | 0, _ => none
  | count + 1, bits => (phase (bits.take width)).or (scan width phase count (bits.drop width))

def value (width : PolynomialBound) (phase : ℕ → BitString → Option (List O))
    (n : ℕ) (bits : BitString) : Option (List O) :=
  scan (width n) (phase n) (bits.length / width n) bits

end ComplexityOfGenerators.Simulation.FixedBlockRetry
