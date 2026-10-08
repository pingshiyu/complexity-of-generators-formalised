import ComplexityOfGenerators.Simulation.PrimitiveOperations
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.Option

/-! Standard sum/product encodings of finite machine instructions, and a proved
primitive-recursive case-analysis interface for their interpreter. -/

namespace ComplexityOfGenerators.Simulation

variable {O : Type} {states symbols : ℕ}

abbrev StepCode (O : Type) (states symbols : ℕ) :=
  Fin states × Option (Fin symbols) × Move × Move × Move × Move × Option O

abbrev InstructionCode (O : Type) (states symbols : ℕ) :=
  Unit ⊕ (Unit ⊕ ((Fin states × Fin states) ⊕ StepCode O states symbols))

def instructionEquiv : Instruction O states symbols ≃ InstructionCode O states symbols where
  toFun
    | .accept => .inl ()
    | .reject => .inr (.inl ())
    | .readRandom f t => .inr (.inr (.inl (f, t)))
    | .step q w m i a n o => .inr (.inr (.inr (q, w, m, i, a, n, o)))
  invFun
    | .inl _ => .accept
    | .inr (.inl _) => .reject
    | .inr (.inr (.inl (f, t))) => .readRandom f t
    | .inr (.inr (.inr (q, w, m, i, a, n, o))) => .step q w m i a n o
  left_inv instruction := by cases instruction <;> rfl
  right_inv code := by
    rcases code with u | u | ⟨f, t⟩ | ⟨q, w, m, i, a, n, o⟩
    · cases u; rfl
    · cases u; rfl
    · rfl
    · rfl

instance [Primcodable O] : Primcodable (Instruction O states symbols) :=
  Primcodable.ofEquiv (InstructionCode O states symbols) instructionEquiv

instance [Finite O] : Finite (Instruction O states symbols) :=
  Finite.of_injective instructionEquiv instructionEquiv.injective

variable {X R : Type} [Primcodable X] [Primcodable R] [Primcodable O]

theorem primrec_instruction_cases {f : X → Instruction O states symbols}
    {accept reject : X → R} {random : X → Fin states × Fin states → R}
    {step : X → StepCode O states symbols → R}
    (hf : Primrec f) (ha : Primrec accept) (hr : Primrec reject)
    (hb : Primrec₂ random) (hs : Primrec₂ step) :
    Primrec (fun x => match f x with
      | .accept => accept x
      | .reject => reject x
      | .readRandom a b => random x (a, b)
      | .step q w m i a n o => step x (q, w, m, i, a, n, o)) := by
  have tail : Primrec₂ (fun (x : X) (code : (Fin states × Fin states) ⊕ StepCode O states symbols) =>
      Sum.casesOn (motive := fun _ => R) code (random x) (step x)) :=
    Primrec.sumCasesOn .snd
      (hb.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (hs.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
  have rest : Primrec₂ (fun (x : X) (code : Unit ⊕ ((Fin states × Fin states) ⊕ StepCode O states symbols)) =>
      Sum.casesOn (motive := fun _ => R) code (fun _ => reject x)
        (fun c => Sum.casesOn (motive := fun _ => R) c (random x) (step x))) :=
    Primrec.sumCasesOn .snd
      (hr.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
      (tail.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
  have core := Primrec.sumCasesOn
    ((Primrec.of_equiv (e := instructionEquiv)).comp hf)
    (ha.comp₂ Primrec₂.left) rest
  exact core.of_eq fun x => by cases f x <;> rfl

end ComplexityOfGenerators.Simulation
