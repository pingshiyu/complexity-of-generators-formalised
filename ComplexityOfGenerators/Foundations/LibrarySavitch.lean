/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey

Adapted from Complexitylib's SavitchReach and SavitchAssemble: the invariant
needed by the recursion is bounded reachable heads, not all-path halting.
-/
import Complexitylib.Classes.Containments.Internal.SavitchAssemble

/-! Savitch reachability for machines that may loop. The library's finite
recursion still terminates; the recognized machine need not. -/

namespace ComplexityOfGenerators.LibrarySavitch
open Complexity Complexity.Cobham
variable {k : ℕ}

section

variable (tm : NTM k) (x : List Bool) (W : ℕ)
  (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : 1 ≤ W)
  (bounded : ∀ c, tm.ReachesCfg (tm.initCfg x) c → CodeInv W c)

include bounded hW hq in
theorem baseReachB_cfgCode {c : Cfg k tm.Q} (hc : tm.ReachesCfg (tm.initCfg x) c)
    (v : List Bool) :
    baseReachB tm (blockRuler W) (Cobham.cfgCode W c) v = true ↔
      ∃ c', tm.ReachesCfgLe 1 c c' ∧ v = Cobham.cfgCode W c' := by
  have hinv : CodeInv W c := bounded c hc
  rw [baseReachB_eq_true_iff]
  by_cases hh : c.state = tm.qhalt
  · rw [nstepFn_code_halted tm false W c hq hinv hh, nstepFn_code_halted tm true W c hq hinv hh]
    constructor
    · intro h
      exact ⟨c, NTM.reachesCfgLe_refl tm 1 c,
        by rcases h with h | h | h <;> exact h.symm⟩
    · rintro ⟨c', hle, rfl⟩
      exact Or.inl (by rw [NTM.eq_of_reachesCfgLe_of_halted hle hh])
  · rw [nstepFn_code tm false W c hq hinv hh, nstepFn_code tm true W c hq hinv hh]
    constructor
    · rintro (h | h | h)
      · exact ⟨c, NTM.reachesCfgLe_refl tm 1 c, h.symm⟩
      · exact ⟨tm.stepCfg false c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, false, rfl⟩), h.symm⟩
      · exact ⟨tm.stepCfg true c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, true, rfl⟩), h.symm⟩
    · rintro ⟨c', hle, rfl⟩
      rcases (NTM.reachesCfgLe_one_iff tm c c').mp hle with rfl | ⟨_, b, rfl⟩
      · exact Or.inl rfl
      · cases b
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)

include bounded hW hq in
theorem baseAccB_cfgCode {c : Cfg k tm.Q} (hc : tm.ReachesCfg (tm.initCfg x) c) :
    baseAccB tm (blockRuler W) (savRuler k (blockRuler W)) (Cobham.cfgCode W c) = true ↔
      ∃ c', tm.ReachesCfgLe 1 c c' ∧ c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one := by
  have hW1 : 1 ≤ W := by omega
  have hruler : W ≤ (savRuler k (blockRuler W)).length := by
    rw [savRuler, wideRuler_length, blockRuler_length, blockWidth]
    have hcb : 1 ≤ codeBlocks k := by rw [codeBlocks]; omega
    calc W ≤ 1 * (2 * (W + 1)) := by omega
      _ ≤ codeBlocks k * (2 * (W + 1)) := Nat.mul_le_mul_right _ hcb
  have hflag : ∀ c'' : Cfg k tm.Q, tm.ReachesCfg (tm.initCfg x) c'' →
      (acceptFlag (stateCode tm.qhalt) (blockRuler W) (savRuler k (blockRuler W))
        (Cobham.cfgCode W c'') = [true] ↔
        c''.state = tm.qhalt ∧ c''.output.cells 1 = Γ.one) := fun c'' hc'' =>
    acceptFlag_cfgCode tm W c'' hq (bounded c'' hc'') hW1 _ hruler
  have hinv : CodeInv W c := bounded c hc
  rw [baseAccB_eq_true_iff]
  by_cases hh : c.state = tm.qhalt
  · rw [nstepFn_code_halted tm false W c hq hinv hh, nstepFn_code_halted tm true W c hq hinv hh,
      hflag c hc]
    constructor
    · intro h
      exact ⟨c, NTM.reachesCfgLe_refl tm 1 c, by rcases h with h | h | h <;> exact h⟩
    · rintro ⟨c', hle, h1, h2⟩
      rw [NTM.eq_of_reachesCfgLe_of_halted hle hh] at h1 h2
      exact Or.inl ⟨h1, h2⟩
  · have hs : ∀ b : Bool, tm.ReachesCfg (tm.initCfg x) (tm.stepCfg b c) := fun b =>
      hc.trans (NTM.reachesCfg_of_reachesCfgLe
        ((NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, b, rfl⟩)))
    rw [nstepFn_code tm false W c hq hinv hh, nstepFn_code tm true W c hq hinv hh,
      hflag c hc, hflag _ (hs false), hflag _ (hs true)]
    constructor
    · rintro (h | h | h)
      · exact ⟨c, NTM.reachesCfgLe_refl tm 1 c, h⟩
      · exact ⟨tm.stepCfg false c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, false, rfl⟩), h⟩
      · exact ⟨tm.stepCfg true c,
          (NTM.reachesCfgLe_one_iff tm c _).mpr (Or.inr ⟨hh, true, rfl⟩), h⟩
    · rintro ⟨c', hle, h1, h2⟩
      rcases (NTM.reachesCfgLe_one_iff tm c c').mp hle with rfl | ⟨_, b, rfl⟩
      · exact Or.inl ⟨h1, h2⟩
      · cases b
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr ⟨h1, h2⟩)

include bounded hW hq in
/-- **The recursion decides bounded reachability.** -/
theorem rchB_cfgCode :
    ∀ (n : ℕ) (c : Cfg k tm.Q), tm.ReachesCfg (tm.initCfg x) c → ∀ v : List Bool,
      Sav.rchB (baseReachB tm (blockRuler W)) (savZero k (blockRuler W)) n
          (Cobham.cfgCode W c) v = true ↔
        ∃ c', tm.ReachesCfgLe (2 ^ n) c c' ∧ v = Cobham.cfgCode W c' := by
  intro n
  induction n with
  | zero =>
      intro c hc v
      rw [Sav.rchB, pow_zero]
      exact baseReachB_cfgCode tm x W hq hW bounded hc v
  | succ n ih =>
      intro c hc v
      rw [Sav.rchB]
      constructor
      · intro h
        obtain ⟨i, _, hP⟩ := Sav.exists_of_anyMid h
        rw [Bool.and_eq_true] at hP
        obtain ⟨cm, hcm, hwm⟩ := (ih c hc _).mp hP.1
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe hcm)
        obtain ⟨c', hc', hv⟩ := (ih cm hcm' v).mp (by rw [← hwm]; exact hP.2)
        exact ⟨c', (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mpr ⟨cm, hcm, hc'⟩, hv⟩
      · rintro ⟨c', hle, rfl⟩
        obtain ⟨cm, h₁, h₂⟩ := (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mp hle
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe h₁)
        refine Sav.anyMid_of_length (w := Cobham.cfgCode W cm) (binValLE_savZero k _) ?_ ?_
        · rw [cfgCode_length, savZero_length]
        · rw [Bool.and_eq_true]
          exact ⟨(ih c hc _).mpr ⟨cm, h₁, rfl⟩, (ih cm hcm' _).mpr ⟨c', h₂, rfl⟩⟩

include bounded hW hq in
/-- **The recursion decides bounded acceptance.** -/
theorem accB_cfgCode :
    ∀ (n : ℕ) (c : Cfg k tm.Q), tm.ReachesCfg (tm.initCfg x) c →
      (Sav.accB (baseReachB tm (blockRuler W))
          (fun u => baseAccB tm (blockRuler W) (savRuler k (blockRuler W)) u)
          (savZero k (blockRuler W)) n (Cobham.cfgCode W c) = true ↔
        ∃ c', tm.ReachesCfgLe (2 ^ n) c c' ∧ c'.state = tm.qhalt ∧
          c'.output.cells 1 = Γ.one) := by
  intro n
  induction n with
  | zero =>
      intro c hc
      rw [Sav.accB, pow_zero]
      exact baseAccB_cfgCode tm x W hq hW bounded hc
  | succ n ih =>
      intro c hc
      rw [Sav.accB]
      constructor
      · intro h
        obtain ⟨i, _, hP⟩ := Sav.exists_of_anyMid h
        rw [Bool.and_eq_true] at hP
        obtain ⟨cm, hcm, hwm⟩ := (rchB_cfgCode tm x W hq hW bounded n c hc _).mp hP.1
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe hcm)
        obtain ⟨c', hc', h1, h2⟩ := (ih cm hcm').mp (by rw [← hwm]; exact hP.2)
        exact ⟨c', (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mpr ⟨cm, hcm, hc'⟩, h1, h2⟩
      · rintro ⟨c', hle, h1, h2⟩
        obtain ⟨cm, hm₁, hm₂⟩ := (NTM.reachesCfgLe_two_pow_succ_iff tm n c c').mp hle
        have hcm' : tm.ReachesCfg (tm.initCfg x) cm :=
          hc.trans (NTM.reachesCfg_of_reachesCfgLe hm₁)
        refine Sav.anyMid_of_length (w := Cobham.cfgCode W cm) (binValLE_savZero k _) ?_ ?_
        · rw [cfgCode_length, savZero_length]
        · rw [Bool.and_eq_true]
          exact ⟨(rchB_cfgCode tm x W hq hW bounded n c hc _).mpr ⟨cm, hm₁, rfl⟩,
            (ih cm hcm').mpr ⟨c', hm₂, h1, h2⟩⟩

end

theorem answer_correct (tm : NTM k) (qp lp : Polynomial ℕ)
    (x : List Bool) (hxW : x.length ≤ qp.eval x.length)
    (hW : 1 ≤ qp.eval x.length)
    (hcardq : Fintype.card tm.Q ≤ blockWidth (qp.eval x.length))
    (bounded : ∀ c, tm.ReachesCfg (tm.initCfg x) c → CodeInv (qp.eval x.length) c)
    {L : Language}
    (hmem : x ∈ L ↔ ∃ c, tm.ReachesCfgLe (2 ^ lp.eval x.length) (tm.initCfg x) c ∧
      tm.halted c ∧ c.output.cells 1 = Γ.one) :
    savAns tm qp lp x = true ↔ x ∈ L := by
  have hR : savR qp x = blockRuler (qp.eval x.length) := savR_eq qp x
  have hfresh := Sav.frameVal_fresh (baseReachB tm (savR qp x))
    (fun u => baseAccB tm (savR qp x) (savRuler k (savR qp x)) u)
    (savZero k (savR qp x)) (binValLE_savZero k _)
    (f := savRoot tm qp lp x) (by rw [savRoot])
  rw [savAns, hfresh]
  have hkind : (savRoot tm qp lp x).kind = true := rfl
  have hu : (savRoot tm qp lp x).u = Cobham.cfgCode (qp.eval x.length) (tm.initCfg x) := by
    rw [savRoot, hR, initRecord_eq tm _ x hxW]
  have hl : (savRoot tm qp lp x).lvl.length = lp.eval x.length := by
    rw [savRoot, polyRuler_length]
  rw [hkind, ite_eq_left rfl, hu, hl, hR]
  rw [accB_cfgCode tm x (qp.eval x.length) hcardq hW bounded _ _
    (NTM.reachesCfg_refl tm _), hmem]


theorem answer_mem_PSPACE (tm : NTM k) (qp lp r w : Polynomial ℕ)
    (hqp : ∀ n, n ≤ qp.eval n)
    (hr : ∀ n, 2 * (2 * (2 * qp.eval n + 2)
        + (lp.eval n + 1) * (2 * (2 * lp.eval n
            + 5 * (codeBlocks k * (2 * qp.eval n + 2)) + 14) + 2) + 14) + 2 + n ≤ r.eval n)
    (hw : ∀ n, (codeBlocks k * (2 * qp.eval n + 2) + 3) * lp.eval n + 2 ≤ w.eval n) :
    {x | savAns tm qp lp x = true} ∈ PSPACE := by
  classical
  -- the standing abbreviations at a fixed input
  set G : List Bool → List Bool := savG tm qp lp with hG
  have hGfp : G ∈ FP := savG_mem_FP tm qp lp
  set Nof : List Bool → ℕ := fun x => savT tm qp lp x + 2 with hNof
  -- the ruler and the widths
  have hRlen : ∀ x : List Bool, (savR qp x).length = 2 * qp.eval x.length + 2 := by
    intro x
    rw [savR_eq, blockRuler_length, blockWidth]
    ring
  have hzlen : ∀ x : List Bool,
      (savZero k (savR qp x)).length = codeBlocks k * (2 * qp.eval x.length + 2) := by
    intro x
    rw [savZero_length, hRlen]
  -- the orbit
  have horb : ∀ (x : List Bool) (j : ℕ), G^[j + 1] (pair [] x)
      = pair (encSst (savR qp x) ((savSemAt tm qp x)^[j] (savInitSst tm qp lp x))) x := by
    intro x j
    rw [hG, savG_iterate]
    rfl
  -- the stack invariant along the orbit
  have hstk : ∀ (x : List Bool) (j : ℕ),
      Sav.StkSize (lp.eval x.length) (codeBlocks k * (2 * qp.eval x.length + 2))
        ((savSemAt tm qp x)^[j] (savInitSst tm qp lp x)).stk := by
    intro x j
    have hxW : x.length ≤ qp.eval x.length := by have := hqp x.length; omega
    have hu : (savRoot tm qp lp x).u.length
        = codeBlocks k * (2 * qp.eval x.length + 2) := by
      rw [savRoot, savR_eq, initRecord_eq tm _ x hxW, cfgCode_length, blockRuler_length,
        blockWidth]
      ring
    have h0 : Sav.StkSize (lp.eval x.length) (codeBlocks k * (2 * qp.eval x.length + 2))
        (savInitSst tm qp lp x).stk := by
      refine ⟨?_, ⟨by rw [hu], ?_, ?_⟩, trivial⟩
      · show ([] : List Sav.Frm).length + (savRoot tm qp lp x).lvl.length = lp.eval x.length
        rw [savRoot]
        simp
      · rw [savRoot]
        exact le_of_eq (hzlen x)
      · rw [savRoot]
        exact le_of_eq (hzlen x)
    exact Sav.iterate_stkSize _ _ _ (le_of_eq (hzlen x)) j _ h0
  -- the four contracts
  have hN : ∀ x : List Bool, Nof x = savT tm qp lp x + 2 := fun _ => rfl
  refine SpaceIter.mem_PSPACE_of_iterate hGfp r w Nof ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- lengths
    intro x i _
    have hbase := hr x.length
    cases i with
    | zero =>
        rw [Function.iterate_zero_apply, pair_length, List.length_nil]
        omega
    | succ j =>
        rw [horb x j, pair_length]
        have := encSst_length_le (Lmax := lp.eval x.length)
          (Wm := codeBlocks k * (2 * qp.eval x.length + 2)) (savR qp x) _ (hstk x j)
        rw [hRlen x] at this
        omega
  · intro x
    rw [hN x]
    omega
  · -- the step count
    intro x
    obtain ⟨hT, _, _, _⟩ := savT_spec tm qp lp x
    have hle := Sav.runBound_le (savZero k (savR qp x)).length (lp.eval x.length)
    have hmono : (2 : ℕ) ^ (((savZero k (savR qp x)).length + 3) * lp.eval x.length + 2)
        ≤ 2 ^ w.eval x.length := by
      refine Nat.pow_le_pow_right (by omega) ?_
      rw [hzlen x]
      exact hw x.length
    rw [hN x]
    omega
  · -- the flag stays down
    intro x i hi hlt
    obtain ⟨_, hdown, _, _⟩ := savT_spec tm qp lp x
    rw [hN x] at hlt
    cases i with
    | zero => omega
    | succ j =>
        rw [horb x j, headD_pair_encSst]
        exact hdown j (by omega)
  · -- the flag goes up
    intro x
    obtain ⟨_, _, hup, _⟩ := savT_spec tm qp lp x
    rw [hN x, show savT tm qp lp x + 2 = savT tm qp lp x + 1 + 1 from rfl,
      horb x (savT tm qp lp x + 1), headD_pair_encSst, hup]
  · intro x
    rw [hN x, show savT tm qp lp x + 2 + 1 = savT tm qp lp x + 2 + 1 from rfl,
      horb x (savT tm qp lp x + 2)]
    intro hc
    have := congrArg List.length hc
    rw [pair_length] at this
    simp at this
  · -- the answer
    intro x
    obtain ⟨_, _, _, hans⟩ := savT_spec tm qp lp x
    rw [hN x, horb x (savT tm qp lp x + 2), headD_pair_encSst, hans]
    rfl


/-- Polynomial space suffices for existential acceptance even if some branches
run forever. Only the constructed deterministic Savitch decider must halt. -/
theorem reachability_mem_PSPACE (tm : NTM k) (p : Polynomial ℕ)
    (space : ∀ x c, tm.ReachesCfg (tm.initCfg x) c →
      c.WithinDecisionSpace x.length (p.eval x.length)) :
    {x | ∃ c, tm.ReachesCfg (tm.initCfg x) c ∧ tm.halted c ∧
      c.output.cells 1 = Γ.one} ∈ PSPACE := by
  classical
  let qp := savWidthPoly (Fintype.card tm.Q) p
  let lp := codeExpBound (Fintype.card tm.Q) k p
  have hqe (n : ℕ) : qp.eval n = n + p.eval n + 1 + Fintype.card tm.Q :=
    savWidthPoly_eval _ _ _
  have hqp (n : ℕ) : n ≤ qp.eval n := by rw [hqe]; omega
  have hW (n : ℕ) : 1 ≤ qp.eval n := by rw [hqe]; omega
  have hq (n : ℕ) : Fintype.card tm.Q ≤ blockWidth (qp.eval n) := by
    rw [blockWidth, hqe]; omega
  have inv (x : List Bool) (c : Cfg k tm.Q) (hc : tm.ReachesCfg (tm.initCfg x) c) :
      CodeInv (qp.eval x.length) c := by
    obtain ⟨hin, hwk, hout⟩ := startInvariant_of_reachesCfg tm x hc
    have hs := space x c hc
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;>
      rw [cfgTapes, List.mem_cons, List.mem_cons, List.mem_ofFn] at ht <;>
      rcases ht with rfl | rfl | ⟨i, rfl⟩
    · exact hin
    · exact hout
    · exact hwk i
    · rw [hqe]; have := hs.1.2; omega
    · rw [hqe]; have := hs.2; omega
    · rw [hqe]; have := hs.1.1 i; omega
  have short (x : List Bool) (c : Cfg k tm.Q) : tm.ReachesCfg (tm.initCfg x) c ↔
      tm.ReachesCfgLe (2 ^ lp.eval x.length) (tm.initCfg x) c := by
    apply NTM.reachesCfg_iff_reachesCfgLe tm _
      (Complexity.cfgCode x.length (p.eval x.length))
    · intro a b ha hb eq
      exact Complexity.cfgCode_inj
        (windowed_of_reachesCfg (space x) (windowed_init tm.qstart x _) ha)
        (space x a ha)
        (windowed_of_reachesCfg (space x) (windowed_init tm.qstart x _) hb)
        (space x b hb) eq
    · exact card_Code_le_two_pow_poly tm.Q k (fun n => p.eval n) p (fun _ => le_rfl) _
  have same : {x | savAns tm qp lp x = true} =
      {x | ∃ c, tm.ReachesCfg (tm.initCfg x) c ∧ tm.halted c ∧ c.output.cells 1 = Γ.one} := by
    ext x
    apply answer_correct tm qp lp x (hqp _) (hW _) (hq _) (inv x)
    simp only [Set.mem_setOf_eq, short x]
  rw [← same]
  exact answer_mem_PSPACE tm qp lp (savStatePoly k qp lp) (savCountPoly k qp lp) hqp
    (fun n => (savStatePoly_eval k qp lp n).symm.le)
    (fun n => (savCountPoly_eval k qp lp n).symm.le)

end ComplexityOfGenerators.LibrarySavitch
