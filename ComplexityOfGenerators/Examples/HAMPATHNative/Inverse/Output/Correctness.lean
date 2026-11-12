import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Output.Basic

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Output

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def headerStore {O : Type} (s : Store) : Store :=
  ((header (O := O)).rename low32).eval
    ((Routine.assign (O := O) 32 2 48 (by decide) (by decide) (by decide) id).eval s)

theorem headerStore_frame {O : Type} (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (scratch : j ≠ 48) : headerStore (O := O) s j = s j := by
  unfold headerStore
  rw [Routine.rename_eval_frame]
  · simp [Routine.assign_eval,scratch,show j ≠ 2 by intro e; have := congrArg Fin.val e; omega]
  · intro i same
    have := congrArg Fin.val same
    dsimp [low32] at this
    omega

theorem headerStore_word {O : Type} (s : Store) (graph : Graph) (start : ℕ)
    (target : s 32 = graph.encode start) :
    headerStore (O := O) s 2 = graph.matrixWord ++ Symbol.separator ::
      (List.range graph.size).map (fun vertex => Symbol.bit (decide (vertex = start))) := by
  change ((header (O := O)).rename low32).eval _ (low32 2) = _
  rw [Routine.rename_eval_here,header_eval]
  simp only [Function.comp_apply,Routine.assign_eval,show low32 2 = 2 from rfl,
    Function.update_self,List.map_id,target]
  rw [headerState_encode]
  simp [rowEncoded,cellEncoded]

theorem matrixPrepare_project {O : Type} (s : Store) (graph : Graph) (start : ℕ)
    (target : s 32 = graph.encode start) (size : (s 35).length = graph.size)
    (position : ℕ) (chosen : (s 40).length = position) :
    ((matrixPrepare (O := O)).eval s) ∘ low16 =
      MatrixInsert.encoded (headerStore (O := O) s ∘ low16) graph.size position (s 45)
        ⟨graph.matrixWord ++ Symbol.separator ::
          (List.range graph.size).map (fun vertex => Symbol.bit (decide (vertex = start))),
          s 44,s 43⟩ [] [] := by
  change ((matrixSetup (O := O)).eval (headerStore (O := O) s)) ∘ low16 = _
  rw [matrixSetup_project,headerStore_word s graph start target,
    headerStore_frame s 35 (by decide) (by decide),
    headerStore_frame s 40 (by decide) (by decide),
    headerStore_frame s 43 (by decide) (by decide),
    headerStore_frame s 44 (by decide) (by decide),
    headerStore_frame s 45 (by decide) (by decide),size,chosen]

theorem matrixPrepare_frame {O : Type} (s : Store) (j : Fin 64) (outside : 32 ≤ j.val)
    (scratch : j ≠ 48) : (matrixPrepare (O := O)).eval s j = s j := by
  change (matrixSetup (O := O)).eval (headerStore (O := O) s) j = _
  rw [matrixSetup_frame _ j (by omega) scratch,headerStore_frame s j outside scratch]

theorem finish_value {O : Type} (s : Store) :
    (finish (O := O)).eval s 31 =
      (s 5).reverse ++ [.separator] ++
        (List.range (s 37).length).map (fun vertex => Symbol.bit (decide (vertex = (s 40).length))) := by
  simp [finish,Routine.seq,Routine.assign_eval,Routine.ofLocal,Local.eval_push,
    OneHot.routine_eval,OneHot.state,markSlots,Routine.clear,Routine.transfer,
    List.map_const',List.reverse_append,List.append_assoc]

theorem routine_graph {O : Type} (s : Store) (graph : Graph) (start position : ℕ)
    (target : s 32 = graph.encode start) (size : (s 35).length = graph.size)
    (parentSize : (s 37).length = graph.size+1) (chosen : (s 40).length = position)
    (fits : position ≤ graph.size) (incoming outgoing : ℕ → Bool)
    (incomingWord : s 44 = (List.range graph.size).map (fun vertex => Symbol.bit (incoming vertex)))
    (outgoingWord : s 45 = (List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))) :
    (routine (O := O)).eval s 31 = (graph.insert position incoming outgoing).encode position := by
  let a := (headerPrefix (O := O)).eval s
  let b := (InsertAt.routine (O := O) newRowSlots (.bit true) (.bit false)).eval a
  let c := (matrixPrepare (O := O)).eval b
  let d := ((MatrixInsert.routine (O := O)).rename low16).eval c
  have bTarget : b 32 = graph.encode start := by simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,target]
  have bSize : (b 35).length = graph.size := by simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,size]
  have bChosen : (b 40).length = position := by simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,chosen]
  have bIncoming : b 44 = (List.range graph.size).map (fun vertex => Symbol.bit (incoming vertex)) := by
    simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,incomingWord]
  have bOutgoing : b 45 =
      ((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))).insertIdx position (.bit false) := by
    have value : b 45 = InsertAt.insertAt
        ((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))) position (.bit false) := by
      simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,outgoingWord,chosen]
    rw [value]
    exact InsertAt.insertAt_eq_insertIdx
      ((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))) position _ (by simpa using fits)
  have bHeader : b 43 = .separator :: List.replicate (graph.size+1) (.bit true) := by
    simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,parentSize]
  have prepared := matrixPrepare_project (O := O) b graph start bTarget bSize position bChosen
  have matrixValue : d 5 = (graph.insert position incoming outgoing).matrixWord.reverse ++ b 43 := by
    change ((MatrixInsert.routine (O := O)).rename low16).eval c (low16 5) = _
    rw [Routine.rename_eval_here]
    change (MatrixInsert.routine (O := O)).eval (((matrixPrepare (O := O)).eval b) ∘ low16) 5 = _
    rw [prepared,bIncoming,bOutgoing,MatrixInsert.routine_graph _ graph position fits]
    simp [MatrixInsert.encoded]
  have dFrame (j : Fin 64) (outside : 32 ≤ j.val) (scratch : j ≠ 48) : d j = b j := by
    change ((MatrixInsert.routine (O := O)).rename low16).eval c j = _
    rw [Routine.rename_eval_frame]
    · exact matrixPrepare_frame b j outside scratch
    · intro i same
      have := congrArg Fin.val same
      dsimp [low16] at this
      omega
  have dParent : (d 37).length = graph.size+1 := by
    rw [dFrame 37 (by decide) (by decide)]
    simp [b,a,InsertAt.routine_eval,newRowSlots,headerPrefix_eval,parentSize]
  have dChosen : (d 40).length = position := by rw [dFrame 40 (by decide) (by decide),bChosen]
  change (finish (O := O)).eval d 31 = _
  rw [finish_value,matrixValue,bHeader,dParent,dChosen]
  simp [Graph.encode,Graph.matrixWord,Graph.insert,List.reverse_append,List.append_assoc]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Output
