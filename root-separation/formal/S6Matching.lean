import S6Asymptotic
import S6UpperWindow
import S6UpperCost
import S6LabelPlacement

namespace Section6

open Finset
open scoped BigOperators
noncomputable section

/-- F.A3 in the paper's log-cardinality form and for every node. -/
theorem FA3_summary
    {V H I A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype A] [LinearOrder A]
    (P : Placement V H I A) (window : Finset ℕ) (R : ℕ) (i : I)
    (hr : 2 ≤ Fintype.card A) (hQ : 256 ≤ Fintype.card I) (hw : window.card = R)
    (hR : 16*R ≤ Fintype.card I)
    (hcap : ∀ u, (loadCell P u : ℝ) * cubeSize I A ≤ 2 * (occupied P).card)
    (hdensity : 2 * (occupied P).card * xi ^ Fintype.card I ≤ (Fintype.card V : ℝ)/2) :
    (Real.exp (-16)/16) * (Fintype.card V : ℝ) *
        Real.exp (-(64*(R : ℝ)^2/Fintype.card I)) ≤
      lg (Set.range (actualSummary P window i)).ncard :=
  (FA3 P window R hr hQ hw hR hcap hdensity).trans
    (le_lg_of_two_pow_le _ _ (FA1 P window i).2)

/-- The upper bound on balanced source labels, with the published numerical
checks exposed. The exceptional rows are exactly those of the centered window.
This is the literal scan bound; the cost of finding the labels is separate. -/
theorem matching_on_balanced_labels {E : Type*} [Fintype E]
    (n r Q R q b lam nu β : ℕ) (v : E → Fin n) (first : Fin n → Fin Q → Fin r)
    (right : E → Fin Q → Fin r) (hv : Function.Surjective v)
    (hcap : ∀ u, Fintype.card (cellFiber (fun e i => (first (v e) i, right e i)) u) *
      cubeSize (Fin Q) (Fin r) ≤ 2 * Fintype.card E)
    (hbal : ∀ (i : Fin Q) (g : Fin r),
      ((univ.filter (fun v => first v i = g)).card : ℝ) ≤ 2 * (n : ℝ) / r)
    (hM : Fintype.card E ≤ b*n)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hR : 32 ≤ R) (hQR : 6*R ≤ Q)
    (hb : 0 < b) (hlam : 0 < lam) (hnu : 1 ≤ nu)
    (hlg : lg lam ≤ nu) (hr₂ : r^2 ≤ lam) (hQL : Q*128*nu ≤ lam)
    (hRL : (β+3)^2*lam ≤ R^2) (hbl : b ≤ lam^β)
    (C d : ℝ) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hq : (q : ℝ) ≤ d*n*((R : ℝ)/Q))
    (hη : (R : ℝ)/Q ≤ C*nu/√(lam : ℝ))
    (hlogη : Real.log (1/((R : ℝ)/Q)) ≤ nu)
    (hrInv : 1/(r : ℝ) ≤ C*(nu : ℝ)^2/√(lam : ℝ))
    (hD : lg (2*(cubeSize (Fin Q) (Fin r) : ℝ)+1) ≤ lam) :
    ∃ h : ℕ, ∃ P : Placement (Fin n) (Fin h) (Fin Q) (Fin r),
      P.first = first ∧
      let maxGroup := (univ : Finset (Fin Q × Fin r)).sup (fun ig =>
        (univ.filter (fun v => P.first v ig.1 = ig.2)).card)
      let rows := Fintype.card (Fin r × (Fin h × Exceptional (Fin Q) (Fin r) (centeredWindow Q R r)))
      lg (scanBound Q r (taylorCount n q) (cubeSize (Fin Q) (Fin r)) rows maxGroup) ≤
        lg (2*(Q : ℝ)*r) + (((d+2)*C/Real.log 2)+4*C)*(n : ℝ)*(nu : ℝ)^2/√(lam : ℝ) := by
  classical
  obtain ⟨h,P,hfirst,_,hcopy,_⟩ := realize_balanced_labels v first right hv hcap
  let D := cubeSize (Fin Q) (Fin r)
  let ε := 1/((b : ℝ)*r^2*lam)
  let window := centeredWindow Q R r
  have hD0 : (0 : ℝ) < D := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    dsimp [D]
    rw [cubeSize_eq]
    simp only [Fintype.card_fin, Nat.cast_pow]
    positivity
  have hExc : (Fintype.card (Exceptional (Fin Q) (Fin r) window) : ℝ) ≤ ε*D := by
    apply (div_le_iff₀ hD0).mp
    have ht := centered_row_tail (I := Fin Q) (A := Fin r) (by simpa using hr)
      (R := R) hR (by simpa using hQR)
    have hu := source_tail_budget lam nu r Q R b β hlam hnu (by omega) hQ hb hlg hr₂ hQL hRL hbl
    exact (by simpa [D,window] using ht : (_ : ℝ) ≤ 2*Real.exp (-((R : ℝ)^2/(64*Q)))).trans hu
  have hbudget := grouped_row_budget (H := Fin h) (I := Fin Q) (A := Fin r) window D
    (Fintype.card E) b n ε (by unfold ε; positivity) (by simpa only [Fintype.card_fin] using hcopy) hM hExc
  have hrows : (Fintype.card (Fin r × (Fin h × Exceptional (Fin Q) (Fin r) window)) : ℝ) ≤
      2*(n : ℝ)/(r*lam) := by
    have he : 2*(Fintype.card (Fin r) : ℝ)*ε*b*n = 2*(n : ℝ)/(r*lam) := by
      simp only [Fintype.card_fin, ε]
      have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      have hbp : (0 : ℝ) < b := by exact_mod_cast hb
      have hlp : (0 : ℝ) < lam := by exact_mod_cast hlam
      field_simp [hrp.ne', hbp.ne', hlp.ne']
    exact hbudget.trans_eq he
  let m (ig : Fin Q × Fin r) := (univ.filter (fun v => P.first v ig.1 = ig.2)).card
  have hmax : (((univ : Finset (Fin Q × Fin r)).sup m : ℕ) : ℝ) ≤ 2*(n : ℝ)/r := by
    have hn : (univ : Finset (Fin Q × Fin r)).Nonempty :=
      ⟨(⟨0,hQ⟩, ⟨0,by omega⟩), mem_univ _⟩
    obtain ⟨x,_,hx⟩ := exists_mem_eq_sup (s := (univ : Finset (Fin Q × Fin r))) hn m
    rw [hx]
    exact (by simpa only [m,hfirst] using hbal x.1 x.2)
  refine ⟨h,P,hfirst,?_⟩
  exact balanced_exp_upper Q n r q D _ _ ((R : ℝ)/Q) lam nu C d hQ (by omega)
    (by have hrp : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
        have hqp : 0 < (Q : ℝ) := by exact_mod_cast hQ
        exact div_pos hrp hqp)
    (by apply (div_le_one (by exact_mod_cast hQ)).mpr; exact_mod_cast (show R ≤ Q by omega))
    (by exact_mod_cast hlam) (by exact_mod_cast hnu) hC hd hq hη hlogη hrInv hrows hD hmax

#print axioms FA3_summary
#print axioms matching_on_balanced_labels

end
end Section6


