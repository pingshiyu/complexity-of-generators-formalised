import ComplexityOfGenerators.Simulation.StarCertification.Basic
import ComplexityOfGenerators.Simulation.UnionGenerator.Views

namespace ComplexityOfGenerators.Simulation.StarCertification
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
noncomputable section

def testFlag (p : PolynomialBound) (j : ℕ) (bits : BitString) : Bool :=
  (UnionGenerator.sourceValue M (IndexwiseCertification.clock p) j
    (bits.take (IndexwiseCertification.seed p j))).isSome

/-- Sequential tests use consecutive disjoint blocks of the supplied finite
word, exactly as the corresponding fresh-stream tests do. -/
def walk (p : PolynomialBound) : ℕ → ℕ → BitString → List Bool × BitString
  | _, 0, bits => ([],bits)
  | start, count+1, bits =>
      let next := walk p (start+1) count (bits.drop (IndexwiseCertification.seed p (start+1)))
      (testFlag M p (start+1) bits::next.1,next.2)

def used (p : PolynomialBound) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, count+1 => IndexwiseCertification.seed p (start+1)+used p (start+1) count

@[simp] theorem walk_length (p : PolynomialBound) (start count : ℕ) (bits : BitString) :
    (walk M p start count bits).1.length = count := by
  induction count generalizing start bits with
  | zero => rfl
  | succ count ih => simp [walk,ih]

theorem walk_remaining (p : PolynomialBound) (start count : ℕ) (bits : BitString) :
    (walk M p start count bits).2 = bits.drop (used p start count) := by
  induction count generalizing start bits with
  | zero => simp [walk,used]
  | succ count ih => simp [walk,used,ih,List.drop_drop,Nat.add_comm]

theorem testFlag_sound (G : UniformGenerators α) (p : PolynomialBound) (j : ℕ) (bits : BitString)
    (accepted : testFlag G.machine p j bits = true) : (G.layer j).Nonempty := by
  obtain ⟨word,value⟩ := Option.isSome_iff_exists.mp accepted
  have run := (UnionGenerator.sourceValue_eq_some G.machine (IndexwiseCertification.clock p) j
    (bits.take (IndexwiseCertification.seed p j)) word).mp value
  exact ⟨word,(bits.take (IndexwiseCertification.seed p j))++[false],by simp,
    G.machine.produces_append _ _ [false] word ⟨_,run⟩⟩

end
end ComplexityOfGenerators.Simulation.StarCertification
