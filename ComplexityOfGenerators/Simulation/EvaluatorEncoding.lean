import ComplexityOfGenerators.Simulation.FiniteEvaluator
import ComplexityOfGenerators.Simulation.InstructionEncoding

/-! Primitive-recursive constructors and projections for the evaluator's
finite data, using Mathlib's sum/product encodings. -/

namespace ComplexityOfGenerators.Simulation

variable {I A O : Type}

def inputDataEquiv : InputData I A ≃ (List I × List A × ℕ) where
  toFun d := (d.input, d.auxiliary, d.index)
  invFun d := ⟨d.1, d.2.1, d.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable I] [Primcodable A] : Primcodable (InputData I A) :=
  Primcodable.ofEquiv (List I × List A × ℕ) inputDataEquiv

variable [Primcodable I] [Primcodable A] [Primcodable O] (M : Machine I A O)

theorem primrec_data_input : Primrec (fun d : InputData I A => d.input) :=
  Primrec.fst.comp (Primrec.of_equiv (e := inputDataEquiv))

theorem primrec_data_auxiliary : Primrec (fun d : InputData I A => d.auxiliary) :=
  (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := inputDataEquiv))

theorem primrec_data_index : Primrec (fun d : InputData I A => d.index) :=
  (Primrec.snd.comp Primrec.snd).comp (Primrec.of_equiv (e := inputDataEquiv))

omit [Primcodable A] [Primcodable O] in
theorem primrec_decisionData : Primrec (fun word : List I => decisionData word) :=
  (Primrec.of_equiv_symm (e := inputDataEquiv)).comp
    (Primrec.id.pair ((Primrec.const []).pair (Primrec.const 0)))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_state : Primrec (fun c : FiniteConfiguration M => c.state) :=
  Primrec.fst.comp (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_inputHead : Primrec (fun c : FiniteConfiguration M => c.inputHead) :=
  (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_auxiliaryHead : Primrec (fun c : FiniteConfiguration M => c.auxiliaryHead) :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_indexHead : Primrec (fun c : FiniteConfiguration M => c.indexHead) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_randomHead : Primrec (fun c : FiniteConfiguration M => c.randomHead) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_workHead : Primrec (fun c : FiniteConfiguration M => c.workHead) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_work : Primrec (fun c : FiniteConfiguration M => c.work) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_visited : Primrec (fun c : FiniteConfiguration M => c.visited) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

omit [Primcodable I] [Primcodable A] in
theorem primrec_config_output : Primrec (fun c : FiniteConfiguration M => c.output) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))).comp
    (Primrec.of_equiv (e := finiteConfigurationEquiv M))

variable {X : Type} [Primcodable X]

omit [Primcodable I] [Primcodable A] in
theorem primrec_configuration_mk {state : X → Fin M.states}
    {inputHead auxiliaryHead indexHead randomHead : X → ℕ} {workHead : X → ℤ}
    {work : X → List (ℤ × Fin M.symbols)} {visited : X → List ℤ} {output : X → List O}
    (hs : Primrec state) (hi : Primrec inputHead) (ha : Primrec auxiliaryHead)
    (hn : Primrec indexHead) (hr : Primrec randomHead) (hh : Primrec workHead)
    (hw : Primrec work) (hv : Primrec visited) (ho : Primrec output) :
    Primrec (fun x => (⟨state x, inputHead x, auxiliaryHead x, indexHead x, randomHead x,
      workHead x, work x, visited x, output x⟩ : FiniteConfiguration M)) :=
  (Primrec.of_equiv_symm (e := finiteConfigurationEquiv M)).comp
    (hs.pair (hi.pair (ha.pair (hn.pair (hr.pair (hh.pair (hw.pair (hv.pair ho))))))))

end ComplexityOfGenerators.Simulation
