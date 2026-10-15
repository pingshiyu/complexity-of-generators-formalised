import ComplexityOfGenerators.Simulation.SavitchMachine.Query
import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateBound
import ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt

/-! Uniform preparation of coordinate queries. Fixed machine-state bounds
are literals in finite control; input and work bounds are computed from the
preserved input by the verified polynomial ruler. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.PrepareQuery

open Turing StackSpace Frames BooleanTest
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type}

inductive Mode | fixed (bound first : ℕ) | input | work

def Mode.bound (space : PolynomialBound) (n : ℕ) : Mode → ℕ
  | .fixed bound _ => bound
  | .input => n + 1
  | .work => 2 * space n + 1

def Mode.first : Mode → ℕ
  | .fixed _ first => first
  | _ => 0

def compile (space : PolynomialBound) (mode : Mode)
    (P : Program (Alphabet α) 6) : Program (Alphabet α) 6 where
  Label := Option (Sum (CoordinateBound.Label space.degree) P.Label)
  finite := inferInstance
  entry := none
  exit := some (.inr P.exit)
  code
    | none => match mode with
      | .fixed bound first => pushCopies 1 (Alphabet.write (some false)) first
          (pushCopies 2 (Alphabet.write (some false)) bound (.goto fun _ => some (.inr P.entry)))
      | _ => .goto fun _ => some (.inl (.ruler .copyInput))
    | some (.inl .done) => .goto fun _ => some (.inr P.entry)
    | some (.inl pc) => embedCode (Function.Embedding.refl _) (some ∘ Sum.inl)
        (CoordinateBound.program (Alphabet.write (some false)) space
          (match mode with | .work => true | _ => false) pc)
    | some (.inr pc) => embedCode (Function.Embedding.refl _) (some ∘ Sum.inr) (P.code pc)
  exit_halts := by simp only [P.exit_halts, embedCode]

theorem trace (space : PolynomialBound) (mode : Mode) (P : Program (Alphabet α) 6)
    (bits : List Bool) (input : List (Alphabet α)) (answer result : Bool) (r : ℕ)
    (bitsRoom : bits.length ≤ r) (inputRoom : input.length ≤ r)
    (rulerRoom : input.length + space input.length + 1 ≤ r)
    (workRoom : 2 * space input.length + 1 ≤ r)
    (boundRoom : mode.bound space input.length ≤ r) (firstRoom : mode.first ≤ r)
    (stk : Fin 7 → List (Alphabet α))
    (query : Trace P.code r
      (localConfig P.entry (carrying answer false)
        (ReadCoordinateAt.before Alphabet.write bits
          ((BoundedDecode.unary mode.first).map Alphabet.write) (mode.bound space input.length) input))
      (localConfig P.exit (carrying answer result) stk)) :
    Trace (compile space mode P).code r
      (localConfig (compile space mode P).entry (carrying answer false) (Query.small bits input))
      (localConfig (compile space mode P).exit (carrying answer result) stk) := by
  classical
  let C := compile space mode P
  let ready := ReadCoordinateAt.before (Alphabet.write (α := α)) bits
    ((BoundedDecode.unary mode.first).map Alphabet.write) (mode.bound space input.length) input
  have initial : ∀ j, (Query.small bits input j).length ≤ r := by
    intro j; fin_cases j <;> simp [Query.small] <;> assumption
  have readyBound : ∀ j, (ready j).length ≤ r := by
    intro j; fin_cases j <;> simp [ready, ReadCoordinateAt.before] <;> assumption
  have prepared : Trace C.code r
      (localConfig C.entry (carrying answer false) (Query.small bits input))
      (localConfig (some (.inr P.entry)) (carrying answer false) ready) := by
    cases mode with
    | fixed bound first =>
        exact .step initial (by
          change some (TM2.stepAux
            (pushCopies 1 (Alphabet.write (some false)) first
              (pushCopies 2 (Alphabet.write (some false)) bound
                (.goto fun _ => (some (.inr P.entry) : C.Label))))
            (carrying answer false, none) (Query.small bits input)) =
              some (localConfig (some (.inr P.entry) : C.Label) (carrying answer false) ready)
          simp only [pushCopies_stepAux, TM2.stepAux, localConfig]
          congr 2
          funext j; fin_cases j <;> simp [Query.small, ready, ReadCoordinateAt.before,
            Mode.first, Mode.bound, List.map_replicate]) (.refl _ readyBound)
    | input =>
        have ruled := CoordinateBound.run (Alphabet.write (α := α) (some false)) space
          false (carrying answer false)
          ((bits.map some).map Alphabet.write) input r (by simpa using bitsRoom) rulerRoom workRoom
        have mapped := ruled.rename_active (by simp [localConfig]) (some ∘ Sum.inl) C.code (by
          intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
        simp only [renameConfig, localConfig, Option.map_some, Function.comp_apply] at mapped
        have layout : CoordinateBound.registers (Alphabet.write (α := α) (some false))
            ((bits.map some).map Alphabet.write) input
            (if false then 2 * space input.length + 1 else input.length + 1) = ready := by
          funext j; fin_cases j <;> simp [CoordinateBound.registers, ready, ReadCoordinateAt.before,
            Mode.bound, Mode.first, List.map_replicate]
        simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false] at layout mapped
        rw [layout] at mapped
        exact .step initial rfl (mapped.trans (.step mapped.end_bound rfl (.refl _ readyBound)))
    | work =>
        have ruled := CoordinateBound.run (Alphabet.write (α := α) (some false)) space
          true (carrying answer false)
          ((bits.map some).map Alphabet.write) input r (by simpa using bitsRoom) rulerRoom workRoom
        have mapped := ruled.rename_active (by simp [localConfig]) (some ∘ Sum.inl) C.code (by
          intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
        simp only [renameConfig, localConfig, Option.map_some, Function.comp_apply] at mapped
        have layout : CoordinateBound.registers (Alphabet.write (α := α) (some false))
            ((bits.map some).map Alphabet.write) input
            (if true then 2 * space input.length + 1 else input.length + 1) = ready := by
          funext j; fin_cases j <;> simp [CoordinateBound.registers, ready, ReadCoordinateAt.before,
            Mode.bound, Mode.first, List.map_replicate]
        simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false] at layout mapped
        rw [layout] at mapped
        exact .step initial rfl (mapped.trans (.step mapped.end_bound rfl (.refl _ readyBound)))
  have last := query.rename (some ∘ Sum.inr) C.code (by intro q; rfl)
  simp only [renameConfig, localConfig, Option.map_some, Function.comp_apply] at last
  exact prepared.trans last

theorem run (space : PolynomialBound) (mode : Mode) (P : Program (Alphabet α) 6)
    (bits : List Bool) (input : List (Alphabet α)) (answer result : Bool) (r : ℕ)
    (bitsRoom : bits.length ≤ r) (inputRoom : input.length ≤ r)
    (rulerRoom : input.length + space input.length + 1 ≤ r)
    (workRoom : 2 * space input.length + 1 ≤ r)
    (boundRoom : mode.bound space input.length ≤ r) (firstRoom : mode.first ≤ r)
    (query : ∃ stk, Trace P.code r
      (localConfig P.entry (carrying answer false)
        (ReadCoordinateAt.before Alphabet.write bits
          ((BoundedDecode.unary mode.first).map Alphabet.write) (mode.bound space input.length) input))
      (localConfig P.exit (carrying answer result) stk) ∧ stk 6 = input) :
    ∃ stk, Trace (compile space mode P).code r
      (localConfig (compile space mode P).entry (carrying answer false) (Query.small bits input))
      (localConfig (compile space mode P).exit (carrying answer result) stk) ∧ stk 6 = input := by
  obtain ⟨stk, traced, preserved⟩ := query
  exact ⟨stk, trace space mode P bits input answer result r bitsRoom inputRoom rulerRoom
    workRoom boundRoom firstRoom stk traced, preserved⟩

end
end ComplexityOfGenerators.Simulation.SavitchMachine.PrepareQuery
