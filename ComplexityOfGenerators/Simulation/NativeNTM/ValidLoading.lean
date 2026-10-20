import ComplexityOfGenerators.Simulation.NativeNTM.Initialization

/-! Valid encodings load precisely the original finite-alphabet input. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)

theorem load_zeros (front rest : BitString) (word : List α) (count : Fin (Fintype.card α + 1))
    (k : ℕ) (room : count.val + k ≤ Fintype.card α) (length : word.length ≤ front.length) :
    InitPath M (front ++ List.replicate k false ++ rest)
      (loading M (front ++ List.replicate k false ++ rest) front.length word count)
      (loading M (front ++ List.replicate k false ++ rest) (front.length + k) word
        ⟨count.val + k, by omega⟩) := by
  induction k generalizing front count with
  | zero => simpa using (Prelude.refl (loading M (front ++ rest) front.length word count))
  | succ k ih =>
    have good : count.val < Fintype.card α := by omega
    have tail := ih (front ++ [false]) ⟨count.val + 1, by omega⟩ (by dsimp; omega) (by simp; omega)
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at tail
    simp only [List.replicate_succ, List.append_assoc, List.cons_append]
    refine .step (loading_bounded M _ _ word count (by simp) (by simp; omega))
      (by intro h; cases h) (fun b => load_zero M b front (List.replicate k false ++ rest) word count good) ?_
    simpa [InitPath, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

theorem load_letter (front rest : BitString) (word : List α) (a : α)
    (length : word.length ≤ front.length) :
    InitPath M (front ++ letterCode a ++ rest)
      (loading M (front ++ letterCode a ++ rest) front.length word 0)
      (loading M (front ++ letterCode a ++ rest) (front ++ letterCode a).length (word ++ [a]) 0) := by
  let rank := Fintype.equivFin α a
  have zeros := load_zeros M front (true :: rest) word 0 rank.val (by simpa using rank.isLt.le) length
  simp only [Fin.val_zero, Nat.zero_add] at zeros
  have same : front ++ List.replicate rank.val false ++ true :: rest = front ++ letterCode a ++ rest := by
    simp [letterCode, rank, List.append_assoc]
  rw [same] at zeros
  refine zeros.trans (.step (loading_bounded M _ _ word _ ?_ ?_) (by intro h; cases h) ?_ (.refl _))
  · simp [letterCode, rank] <;> omega
  · simp [letterCode] <;> omega
  · intro b
    have one := load_one M b (front ++ List.replicate rank.val false) rest word
      ⟨rank.val, by omega⟩ rank.isLt
    simpa [letterCode, rank, List.append_assoc, Nat.add_assoc] using one

theorem load_encoded (front : BitString) (word tail : List α) (length : word.length ≤ front.length) :
    InitPath M (front ++ encode tail)
      (loading M (front ++ encode tail) front.length word 0)
      (loading M (front ++ encode tail) (front ++ encode tail).length (word ++ tail) 0) := by
  induction tail generalizing front word with
  | nil => simpa using (Prelude.refl (loading M front front.length word 0))
  | cons a tail ih =>
    have first := load_letter M front (encode tail) word a length
    have rest := ih (front ++ letterCode a) (word ++ [a]) (by simp [letterCode] <;> omega)
    simp only [encode_cons, ← List.append_assoc]
    have joined := first.trans rest
    simpa [InitPath, List.append_assoc] using joined

theorem encoded_init (word : List α) :
    InitPath M (encode word) ((tm M).initCfg (encode word))
      (simulated M (encode word) word (M.decisionView M.initialConfiguration) false 0) := by
  have loaded := load_encoded M [] [] word (by simp)
  simp only [List.nil_append, List.length_nil] at loaded
  have len := (encode_length word).1
  exact (boot_path M (encode word)).trans (loaded.trans
    (.step (loading_bounded M (encode word) (encode word).length word 0 le_rfl len)
      (by intro h; cases h) (fun b => load_end M b (encode word) word)
      (rewind_path M (encode word) word word.length len)))

end
end ComplexityOfGenerators.Simulation.NativeNTM
