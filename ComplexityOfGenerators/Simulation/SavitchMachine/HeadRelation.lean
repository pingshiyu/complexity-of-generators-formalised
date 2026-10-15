import ComplexityOfGenerators.Simulation.SavitchMachine.HeadComparison
import ComplexityOfGenerators.Simulation.SavitchMachine.Endpoint
import ComplexityOfGenerators.Simulation.SavitchMachine.Alphabet

/-! Compare the same header field in two endpoint columns. The first field is
parsed to a bounded unary coordinate; the second endpoint is then loaded from
its preserved column. Malformed fields reject without growing an unbounded
counter. Both the input and the endpoint column survive the query. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.HeadRelation

open Turing StackSpace Frames
set_option backward.isDefEq.respectTransparency false
variable {α : Type}

inductive Label
  | read (pc : ReadCoordinateAt.Label) | transfer | load (pc : Endpoint.Label)
  | reset | compare (pc : HeadComparison.Label) | reject | done
  deriving DecidableEq, Fintype

def program (a b : ℕ) (direction : Move) (clamp : Bool) :
    Label → Stmt (Alphabet α) Label (Status × Option (Alphabet α)) 7
  | .read .done => .branch (fun v => v.1.returned.getD false)
      (.goto fun _ => .transfer) (.goto fun _ => .reject)
  | .read pc => embedCode (Function.Embedding.refl _) Label.read
      (extendCode (ReadCoordinateAt.program Alphabet.write Alphabet.read a b pc))
  | .transfer => transferCode 0 1 .transfer (.load .load) (fun _ => true)
  | .load .done => .goto fun _ => .reset
  | .load pc => embedCode (Function.Embedding.refl _) Label.load
      (Endpoint.program (Alphabet.write none) (fun s => (Alphabet.read s).isSome) pc)
  | .reset => .load (fun v => (carrying v.1.answer false, none))
      (.goto fun _ => .compare (.read (.skip .copy)))
  | .compare .done => .goto fun _ => .done
  | .compare pc => embedCode (Function.Embedding.refl _) Label.compare
      (extendCode (HeadComparison.program Alphabet.write Alphabet.read a b direction clamp pc))
  | .reject => .load (fun v => (carrying v.1.answer false, none)) (.goto fun _ => .done)
  | .done => .halt

def test (a b n bound : ℕ) (direction : Move) (clamp : Bool) (u v : List Bool) : Bool :=
  ((FixedWidthCodec.fin bound).decode ((u.drop (a * n + b)).take bound)).any fun first =>
    ((FixedWidthCodec.fin bound).decode ((v.drop (a * n + b)).take bound)).any fun last =>
      decide (MoveCheck.destination direction clamp (bound - 1) first.val = some last.val)

/-- Exact two-endpoint coordinate test. The column can contain any suspended
parent fields; its contents are restored even when the query rejects. -/
theorem run (a b : ℕ) (direction : Move) (clamp answer : Bool)
    (u v : List Bool) (input parents : List (Alphabet α)) (bound r : ℕ)
    (sourceRoom : u.length ≤ r) (inputRoom : input.length ≤ r)
    (columnRoom : v.length + 1 + parents.length ≤ r)
    (offsetRoom : a * input.length + b ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    let column := (v.map some).map Alphabet.write ++ Alphabet.write none :: parents
    ∃ stk, Trace (program a b direction clamp) r
      (localConfig (.read (.skip .copy)) (carrying answer false)
        (Fin.snoc (ReadCoordinateAt.before Alphabet.write u [] bound input) column))
      (localConfig .done (carrying answer (test a b input.length bound direction clamp u v)) stk) ∧
      stk 6 = input ∧ stk 7 = column := by
  let P := program (α := α) a b direction clamp
  let column := (v.map some).map (Alphabet.write (α := α)) ++ Alphabet.write none :: parents
  have columnBound : column.length ≤ r := by simp only [column, List.length_append, List.length_map, List.length_cons]; omega
  obtain ⟨value, parsed, valueBound, exactValue⟩ := ReadCoordinateAt.run
    (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse a b answer u [] input bound r
    sourceRoom (by simp) inputRoom offsetRoom counterRoom
  have first := (parsed.extend column columnBound).rename_active
    (by simp [extendConfig, localConfig]) Label.read P (by
      intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, extendConfig, localConfig, Option.map_some] at first
  let sourceField := (u.drop (a * input.length + b)).take bound
  let decodedMemory : Fin 8 → List (Alphabet α) := Fin.snoc (ReadCoordinateAt.after (Alphabet.write (α := α)) value [] bound input) column
  change Trace P r _ (localConfig (.read .done)
    (carrying answer ((FixedWidthCodec.fin bound).decode sourceField).isSome) decodedMemory) at first
  cases decoded : (FixedWidthCodec.fin bound).decode sourceField with
  | none =>
      simp only [decoded, Option.isSome_none] at first
      have rejected : test a b input.length bound direction clamp u v = false := by
        simp only [test, show (u.drop (a * input.length + b)).take bound = sourceField from rfl,
          decoded, Option.any_none]
      refine ⟨decodedMemory, ?_, ?_, ?_⟩
      · rw [rejected]
        exact first.trans (.step first.end_bound rfl
          (.step first.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying])
            (.refl _ first.end_bound)))
      · change Fin.snoc _ _ (Fin.castSucc (6 : Fin 7)) = _
        simp [decodedMemory, ReadCoordinateAt.after]
      · exact Fin.snoc_last _ _
  | some head =>
      have equal := exactValue head decoded
      subst value
      simp only [decoded, Option.isSome_some] at first
      have moved := transfer_all P 0 1 (by decide) .transfer (.load .load) (fun _ => true) rfl
        (carrying answer true) decodedMemory (by simp) r first.end_bound (by
          simpa [decodedMemory, ReadCoordinateAt.after] using (show head.val ≤ r by omega))
      let ready : Fin 8 → List (Alphabet α) := Fin.snoc (ReadCoordinateAt.before (Alphabet.write (α := α)) []
        ((BoundedDecode.unary head.val).map Alphabet.write) bound input) column
      have transferLayout : replaceTwo decodedMemory (0 : Fin 8) 1 []
          ((decodedMemory 0).reverse ++ decodedMemory 1) = ready := by
        funext j; fin_cases j <;>
          simp [replaceTwo, decodedMemory, ready, ReadCoordinateAt.before, ReadCoordinateAt.after,
            List.map_reverse, List.reverse_replicate]
      rw [transferLayout] at moved
      have loaded := Endpoint.run (Alphabet.write (α := α) none) (fun s => (Alphabet.read s).isSome)
        (carrying answer true) ready ((v.map some).map Alphabet.write) parents (by exact Fin.snoc_last _ _)
        (by intro s hs; simp only [List.mem_map] at hs; rcases hs with ⟨s, hs, rfl⟩
            rcases hs with ⟨bit, hb, rfl⟩; rfl) rfl (by simp [ready, ReadCoordinateAt.before])
        (by simp [ready, ReadCoordinateAt.before]) (by simp [ready, ReadCoordinateAt.before]) r moved.end_bound
      have second := loaded.rename_active (by simp [localConfig]) Label.load P (by
        intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
      simp only [renameConfig, localConfig, Option.map_some] at second
      let targetReady : Fin 8 → List (Alphabet α) := Fin.snoc (ReadCoordinateAt.before (Alphabet.write (α := α)) v
        ((BoundedDecode.unary head.val).map Alphabet.write) bound input) column
      have loadLayout : Function.update ready (0 : Fin 8) ((v.map some).map Alphabet.write) = targetReady := by
        funext j; fin_cases j <;> simp [ready, targetReady, ReadCoordinateAt.before]
      rw [loadLayout] at second
      obtain ⟨final, compared, inputPreserved⟩ := HeadComparison.run
        (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse a b direction clamp answer v input
        head.val bound r head.isLt (by omega) inputRoom offsetRoom counterRoom
      have last := (compared.extend column columnBound).rename_active
        (by simp [extendConfig, localConfig]) Label.compare P (by
          intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
      simp only [renameConfig, extendConfig, localConfig, Option.map_some] at last
      have result : test a b input.length bound direction clamp u v =
          ((FixedWidthCodec.fin bound).decode ((v.drop (a * input.length + b)).take bound)).any
            (fun target => decide (MoveCheck.destination direction clamp (bound - 1) head.val = some target.val)) := by
        simp only [test, show (u.drop (a * input.length + b)).take bound = sourceField from rfl,
          decoded, Option.any_some]
      refine ⟨(Fin.snoc final column : Fin 8 → List (Alphabet α)), ?_, ?_, Fin.snoc_last _ _⟩
      · rw [result]
        exact first.trans (.step first.end_bound rfl (moved.trans
          (second.trans (.step second.end_bound rfl
            (.step second.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying, targetReady])
              (last.trans (.step last.end_bound rfl (.refl _ last.end_bound))))))))
      · change (Fin.snoc final column : Fin 8 → List (Alphabet α)) (Fin.castSucc (6 : Fin 7)) = input
        rw [Fin.snoc_castSucc, inputPreserved]

end ComplexityOfGenerators.Simulation.SavitchMachine.HeadRelation
