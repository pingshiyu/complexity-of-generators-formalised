import Complexitylib.Classes.Containments.Internal.ConfigGraph

/-! Choice-independent initialization can be separated from an NTM's later
computation. Bounds cover every prefix, including malformed inputs. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
variable {k : ℕ} {tm : NTM k} {P : Cfg k tm.Q → Prop}

inductive Prelude (tm : NTM k) (P : Cfg k tm.Q → Prop) :
    Cfg k tm.Q → Cfg k tm.Q → Prop
  | refl (c) : Prelude tm P c c
  | step {c d e} : P c → c.state ≠ tm.qhalt → (∀ b, tm.stepCfg b c = d) →
      Prelude tm P d e → Prelude tm P c e

namespace Prelude
variable {a b c : Cfg k tm.Q}

theorem trans (first : Prelude tm P a b) (second : Prelude tm P b c) : Prelude tm P a c := by
  induction first with
  | refl => exact second
  | step bound live next _ ih => exact .step bound live next (ih second)

theorem reaches (path : Prelude tm P a b) : tm.ReachesCfg a b := by
  induction path with
  | refl => exact .refl
  | step bound live next _ ih => exact ih.head ⟨live, false, (next false).symm⟩

/-- Every reachable configuration is an initialization prefix or is reachable
from its endpoint. The prefix alternative is explicitly nonterminal. -/
theorem factor (init : Prelude tm P a b) (path : tm.ReachesCfg a c) :
    (P c ∧ c.state ≠ tm.qhalt) ∨ tm.ReachesCfg b c := by
  induction init with
  | refl => exact Or.inr path
  | @step a d b bound live next tail ih =>
    rcases path.cases_head with rfl | ⟨d', ⟨_, bit, eq⟩, rest⟩
    · exact Or.inl ⟨bound, live⟩
    · have same : d' = d := eq.trans (next bit)
      rw [same] at rest
      exact ih rest

theorem accepting_iff (init : Prelude tm P a b) :
    (∃ c, tm.ReachesCfg a c ∧ tm.halted c ∧ c.output.cells 1 = .one) ↔
      ∃ c, tm.ReachesCfg b c ∧ tm.halted c ∧ c.output.cells 1 = .one := by
  constructor
  · rintro ⟨c, path, halt, output⟩
    rcases init.factor path with ⟨_, live⟩ | after
    · exact (live halt).elim
    · exact ⟨c, after, halt, output⟩
  · rintro ⟨c, path, halt, output⟩
    exact ⟨c, init.reaches.trans path, halt, output⟩

end Prelude
end ComplexityOfGenerators.Simulation.NativeNTM
