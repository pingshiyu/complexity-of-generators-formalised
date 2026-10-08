import ComplexityOfGenerators.Cryptography
import ComplexityOfGenerators.Foundations.ResourceBounds
import VCVio.CryptoFoundations.Asymptotics.Security
import Mathlib.Computability.Encoding
import Mathlib.Order.Filter.Cofinite

/-!
# Cryptographic foundations for the separation theorem

The paper's collision-resistance assumption is retained: unkeyed hashes, uniform
polynomial-time attacks, and inverse-polynomial success on infinitely many sizes.
VCVio's `negligible` and `SecurityGame` provide the security API. The bridges below
relate those definitions to the paper's exact quantifiers; no keyed or nonuniform
assumption is substituted.
-/

namespace ComplexityOfGenerators

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Pigeonhole: compression by one bit forces a collision at every parameter.
This uses Mathlib's finite-cardinality theorem, with no security assumption. -/
theorem HashFunction.collision_exists (h : HashFunction) (n : ℕ) :
    ∃ a b : Bits (n + 1), a ≠ b ∧ h.hash n a = h.hash n b := by
  have bigger : Fintype.card (Bits n) < Fintype.card (Bits (n + 1)) := by
    simp only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [pow_succ]
    have positive : 0 < (2 : ℕ) ^ n := pow_pos (by omega) _
    omega
  have notInjective : ¬ Function.Injective (h.hash n) := by
    intro injective
    exact Nat.not_le_of_lt bigger (Fintype.card_le_of_injective _ injective)
  classical
  simp only [Function.Injective, not_forall] at notInjective
  obtain ⟨a, b, same, different⟩ := notInjective
  exact ⟨a, b, different, same⟩

/-- Corrected, typed Definition 5.5: preimages of `h_n` have length `n+1`.
Pair serialization is explicit and independent of its security parameter. -/
def HashFunction.collisionLanguage (h : HashFunction) : Language PairSymbol :=
  { w | ∃ n x y, h.IsCollision n x y ∧ w = encodePair x y }

@[simp] theorem bitsWord_length {n : ℕ} (x : Bits n) : (bitsWord x).length = n := by
  simp [bitsWord]

@[simp] theorem encodePair_length (x y : BitString) :
    (encodePair x y).length = x.length + y.length + 1 := by
  simp [encodePair]
  omega

/-- Every security parameter gives a nonempty, precisely sized collision slice. -/
theorem HashFunction.collision_slice_nonempty (h : HashFunction) (n : ℕ) :
    (lengthSlice h.collisionLanguage (2 * (n + 1) + 1)).Nonempty := by
  obtain ⟨a, b, different, equalHash⟩ := h.collision_exists n
  refine ⟨encodePair (bitsWord a) (bitsWord b), ?_, ?_⟩
  · exact ⟨n, bitsWord a, bitsWord b, ⟨a, b, rfl, rfl, different, equalHash⟩, rfl⟩
  · simp
    omega

private def decodeBits : List PairSymbol → Option BitString
  | [] => some []
  | .separator :: _ => none
  | .bit b :: tail => (decodeBits tail).map (b :: ·)

def decodePair : List PairSymbol → Option (BitString × BitString)
  | [] => none
  | .separator :: tail => (decodeBits tail).map (fun y => ([], y))
  | .bit b :: tail => (decodePair tail).map (fun p => (b :: p.1, p.2))

private theorem decodeBits_map (x : BitString) :
    decodeBits (x.map PairSymbol.bit) = some x := by
  induction x with
  | nil => rfl
  | cons b tail ih => simp [decodeBits, ih]

@[simp] theorem decodePair_encode (x y : BitString) :
    decodePair (encodePair x y) = some (x, y) := by
  induction x with
  | nil => simp [encodePair, decodePair, decodeBits_map]
  | cons b tail ih =>
      simpa [encodePair, decodePair] using
        congrArg (Option.map (fun p : BitString × BitString => (b :: p.1, p.2))) ih

private theorem decodeBits_sound (word : List PairSymbol) (bits : BitString)
    (decoded : decodeBits word = some bits) : word = bits.map PairSymbol.bit := by
  induction word generalizing bits with
  | nil => simpa [decodeBits] using decoded
  | cons symbol tail ih =>
      cases symbol with
      | separator => simp [decodeBits] at decoded
      | bit b =>
          cases rest : decodeBits tail with
          | none => simp [decodeBits, rest] at decoded
          | some bs =>
              have same : b :: bs = bits := by simpa [decodeBits, rest] using decoded
              subst bits
              simp [ih bs rest]

/-- The parser rejects missing or additional separators; every successful
parse is the canonical encoding of the returned pair. -/
theorem decodePair_sound (word : List PairSymbol) (x y : BitString)
    (decoded : decodePair word = some (x, y)) : word = encodePair x y := by
  induction word generalizing x y with
  | nil => simp [decodePair] at decoded
  | cons symbol tail ih =>
      cases symbol with
      | separator =>
          cases rest : decodeBits tail with
          | none => simp [decodePair, rest] at decoded
          | some bs =>
              have same : ([], bs) = (x, y) := by simpa [decodePair, rest] using decoded
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj same.symm
              simp [encodePair, decodeBits_sound tail y rest]
      | bit b =>
          cases rest : decodePair tail with
          | none => simp [decodePair, rest] at decoded
          | some pair =>
              have same : (b :: pair.1, pair.2) = (x, y) := by simpa [decodePair, rest] using decoded
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj same.symm
              simp [encodePair, ih pair.1 pair.2 rest]

/-- Reuse Mathlib's finite-encoding interface instead of inventing another codec. -/
def collisionPairEncoding : Computability.Encoding (BitString × BitString) PairSymbol where
  encode := fun p => encodePair p.1 p.2
  decode := decodePair
  decode_encode := fun p => decodePair_encode p.1 p.2

theorem encodePair_injective :
    Function.Injective (fun p : BitString × BitString => encodePair p.1 p.2) :=
  collisionPairEncoding.encode_injective

/-- Exact inverse-polynomial formulation corresponding to Definition 5.4. -/
def InversePolynomialNegligible (f : ℕ → ℝ≥0∞) : Prop :=
  ∀ q : PolynomialBound, ∀ᶠ n in atTop, f n ≤ (q n : ℝ≥0∞)⁻¹

/-- The paper's inverse-polynomial quantifiers agree exactly with VCVio's
superpolynomial-decay definition, including arbitrary constant factors. -/
theorem inversePolynomialNegligible_iff (f : ℕ → ℝ≥0∞) :
    InversePolynomialNegligible f ↔ negligible f := by
  constructor
  · intro small k
    let q : PolynomialBound := ⟨1, k + 1, by decide⟩
    have upper : ∀ᶠ (n : ℕ) in atTop,
        (↑n : ℝ≥0∞) ^ k * f n ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      filter_upwards [small q] with n hn
      have base_ne_zero : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
      have base_ne_top : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
      have power_ne_zero := pow_ne_zero k base_ne_zero
      have power_ne_top : (((n + 1 : ℕ) : ℝ≥0∞) ^ k) ≠ ⊤ := by simp
      have bound : (n : ℝ≥0∞) ^ k ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ k :=
        pow_le_pow_left' (by exact_mod_cast Nat.le_succ n) k
      calc
        (n : ℝ≥0∞) ^ k * f n ≤
            ((n + 1 : ℕ) : ℝ≥0∞) ^ k * (q n : ℝ≥0∞)⁻¹ :=
          mul_le_mul' bound hn
        _ = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          simp only [q, PolynomialBound.eval, one_mul, Nat.cast_pow]
          rw [pow_succ, ENNReal.mul_inv (.inl power_ne_zero) (.inl power_ne_top),
            ← mul_assoc, ENNReal.mul_inv_cancel power_ne_zero power_ne_top, one_mul]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (Eventually.of_forall fun _ => zero_le) upper
  · intro small q
    have converges := (negligible_polynomial_mul small q.asPolynomial) 0
    simp only [pow_zero, one_mul, PolynomialBound.asPolynomial_eval] at converges
    filter_upwards [converges.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < 1))]
      with n hn
    exact ENNReal.le_inv_iff_mul_le.mpr (by simpa [mul_comm] using hn.le)

theorem no_infinite_violations_iff (f : ℕ → ℝ≥0∞) (q : PolynomialBound) :
    ¬ Set.Infinite {n : ℕ | (q n : ℝ≥0∞)⁻¹ < f n} ↔
      ∀ᶠ n in atTop, f n ≤ (q n : ℝ≥0∞)⁻¹ := by
  rw [← Nat.frequently_atTop_iff_infinite]
  simp only [Filter.Frequently, not_not, not_lt]

/-- Replaces “no attack succeeds on infinitely many sizes” by an eventual bound,
without changing its quantifier order or its strict/non-strict inequalities. -/
theorem HashFunction.collisionResistant_iff_eventual (h : HashFunction) :
    h.CollisionResistant ↔
      ∀ A : CollisionFinder, InversePolynomialNegligible
        (fun n => fairCoinMeasure (collisionSuccess h A n)) := by
  simp only [HashFunction.CollisionResistant, not_exists, InversePolynomialNegligible]
  exact forall_congr' fun A => forall_congr' fun q => no_infinite_violations_iff _ q

/-- VCVio security-game interface. `CollisionFinder` already bundles one uniform
polynomial-time machine, so the efficient adversary predicate is `True`. -/
noncomputable def collisionGame (h : HashFunction) : SecurityGame CollisionFinder where
  advantage := fun A n => fairCoinMeasure (collisionSuccess h A n)

/-- The exact collision-resistance assumption used in Theorems 5.1 and 7.2,
expressed as a VCVio security game over uniform polynomial-time finders. -/
theorem HashFunction.collisionResistant_iff_vcvio (h : HashFunction) :
    h.CollisionResistant ↔ (collisionGame h).secureAgainst (fun _ => True) := by
  rw [h.collisionResistant_iff_eventual]
  simp only [SecurityGame.secureAgainst, collisionGame, true_implies]
  exact forall_congr' fun A => inversePolynomialNegligible_iff _

end ComplexityOfGenerators
