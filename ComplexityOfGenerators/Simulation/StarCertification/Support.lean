import ComplexityOfGenerators.Simulation.StarCertification.Iteration
import ComplexityOfGenerators.Simulation.StarCertification.Blocks

namespace ComplexityOfGenerators.Simulation.StarCertification
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true

/-- Cached test j reads the jth consecutive fresh block, without reusing an
earlier test's random suffix. -/
theorem walk_lookup (p : PolynomialBound) (start count : ℕ) (bits : BitString) (k : ℕ) (inside : k < count) :
    (walk M p start count bits).1[k]? =
      some (testFlag M p (start+k+1) (bits.drop (used p start k))) := by
  induction count generalizing start bits k with
  | zero => omega
  | succ count ih =>
      cases k with
      | zero => simp [walk,used]
      | succ k =>
          have next := ih (start+1) (bits.drop (IndexwiseCertification.seed p (start+1))) k (by omega)
          simpa only [walk,List.getElem?_cons_succ,used,List.drop_drop,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using next

/-- Every true cache flag certifies an actually nonempty source layer,
including when the caller supplies fewer coins than the chosen width. -/
theorem walk_sound (G : UniformGenerators α) (p : PolynomialBound) (start count : ℕ) (bits : BitString)
    (j : ℕ) (positive : 0 < j) (inside : j ≤ count)
    (available : ((walk G.machine p start count bits).1[j-1]?).getD false = true) :
    (G.layer (start+j)).Nonempty := by
  rw [walk_lookup G.machine p start count bits (j-1) (by omega)] at available
  simp only [Option.getD_some] at available
  have result := testFlag_sound G p (start+(j-1)+1) (bits.drop (used p start (j-1))) available
  have index : start+(j-1)+1 = start+j := by omega
  simpa only [index] using result

/-- The cache's global alphabet representation is directly compatible with
the small-alphabet native StarPaths selector. -/
theorem cacheWord_pathEncoding (flags : List Bool) :
    cacheWord M flags = (StarPaths.flagsWord flags).map (Sum.inr : StarPaths.Symbol → Cell M) := by
  simp only [cacheWord,StarPaths.flagsWord,List.map_map,Function.comp_def]
  rfl

end ComplexityOfGenerators.Simulation.StarCertification
