import ComplexityOfGenerators.Foundations.FixedWidthCodec

/-! Length soundness of configuration codecs. Decoding success certifies an
entire fixed-width field, including for products and finite tape windows. -/

namespace ComplexityOfGenerators.FixedWidthCodec

variable {V W : Type}

def Exact (c : FixedWidthCodec V) : Prop :=
  ∀ bits value, c.decode bits = some value → bits.length = c.width

theorem exact_fin (m : ℕ) : Exact (fin m) := by
  intro bits value decoded
  simp only [fin] at decoded ⊢
  split_ifs at decoded with valid
  · exact valid.1

theorem Exact.transport {c : FixedWidthCodec V} (exact : Exact c) (e : V ≃ W) :
    Exact (c.transport e) := by
  intro bits value decoded
  obtain ⟨v, hv, _⟩ := Option.map_eq_some_iff.mp decoded
  exact exact bits v hv

theorem exact_optionFin (m : ℕ) : Exact (optionFin m) :=
  (exact_fin (m + 1)).transport (finSuccEquiv m)

theorem Exact.prod {c : FixedWidthCodec V} {d : FixedWidthCodec W}
    (left : Exact c) (right : Exact d) : Exact (c.prod d) := by
  intro bits value decoded
  cases hv : c.decode (bits.take c.width) with
  | none => simp [FixedWidthCodec.prod, hv] at decoded
  | some v =>
    cases hw : d.decode (bits.drop c.width) with
    | none => simp [FixedWidthCodec.prod, hv, hw] at decoded
    | some w =>
      have first := left _ _ hv
      have last := right _ _ hw
      simp only [List.length_take] at first
      simp only [List.length_drop] at last
      change bits.length = c.width + d.width
      omega

theorem Exact.vector {c : FixedWidthCodec V} (exact : Exact c) (n : ℕ) : Exact (c.vector n) := by
  induction n with
  | zero =>
      intro bits value decoded
      simp only [FixedWidthCodec.vector] at decoded ⊢
      split_ifs at decoded with empty
      · simp [empty]
  | succ n ih => exact (exact.prod ih).transport _

theorem Exact.decode_short {c : FixedWidthCodec V} (exact : Exact c) (bits : List Bool)
    (short : bits.length < c.width) : c.decode bits = none := by
  cases h : c.decode bits with
  | none => rfl
  | some value => have eq := exact bits value h; omega

end ComplexityOfGenerators.FixedWidthCodec
