import ComplexityOfGenerators.Simulation.WordStack.TransferWhile
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Simulation.WordStack
variable {S O : Type} {k : ℕ} {s : Local.Store S k} {budget : ℕ}

theorem StoreBound.transferWhile (sizes : StoreBound s budget) (src dst : Fin k) (different : src ≠ dst)
    (keep : S → Bool) (f : S → S) (empty : s dst = []) :
    StoreBound ((Routine.transferWhile (O := O) src dst different keep f).eval s) budget := by
  change StoreBound (Function.update (Function.update s src ((s src).dropWhile keep)) dst
    (((s src).takeWhile keep).reverse.map f++s dst)) budget
  apply (sizes.update src _ ((List.dropWhile_sublist keep).length_le.trans (sizes src))).update dst _ ?_
  simpa only [empty,List.append_nil,List.length_map,List.length_reverse] using
    (List.takeWhile_sublist (l := s src) keep).length_le.trans (sizes src)

theorem Routine.transferWhile_cost (src dst : Fin k) (different : src ≠ dst) (keep : S → Bool)
    (f : S → S) (sizes : StoreBound s budget) :
    (Routine.transferWhile (O := O) src dst different keep f).cost s ≤ 6*budget :=
  Nat.mul_le_mul_left 6 ((List.takeWhile_sublist (l := s src) keep).length_le.trans (sizes src))
end ComplexityOfGenerators.Simulation.WordStack
