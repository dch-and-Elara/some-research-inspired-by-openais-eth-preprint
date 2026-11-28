import J6R16ModeCostSite

/-! Polynomial envelopes for the bit-width and catalogue length.
Canonical encodings below describe the supplied input tape; producing
that tape or a child tensor is not charged by this meter. -/
namespace J6R16ModeCost
open scoped BigOperators Polynomial Classical
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint
open J6R11Blueprint J6R15ModeCost J6R10Repack

def precisionSize (s C : ℕ) : ℕ := siteConstant C*(C*s)*s

def uniformWidth (s C : ℕ) : ℕ := precisionSize s C+1

def rosterSize (s C : ℕ) : ℕ := (6*(C*s))*precisionSize s C

def uniformFee (s C : ℕ) : ℕ := localFeeCap (uniformWidth s C) (rosterSize s C)

theorem localFee_mono (q : ℕ) {n m : ℕ} (h : n≤m) : localFeeCap q n≤localFeeCap q m := by
  unfold localFeeCap setupCap delayCap transitionCap scanCap
  gcongr

theorem raw_width_fits (s C p : ℕ) (hp : p≤precisionSize s C) : p<2^uniformWidth s C := by
  have hQ := J9PrintedSchedule.next_le_two_power (uniformWidth s C)
  unfold uniformWidth at hQ ⊢
  omega

theorem full_roster_length {A : Type*} [Fintype A] (ms : List A)
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) : ms.length=Nat.card A := by
  classical
  have hs : ms.toFinset=(Finset.univ : Finset A) := by ext x; simp [hall x]
  rw [← List.toFinset_card_of_nodup hm,hs,Finset.card_univ,Nat.card_eq_fintype_card]

theorem physical_roster_length {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a p : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a)
    (ms : List (J6R15ModeCost.Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p))
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) :
    ms.length≤(6*Nat.card E)*p := by
  let I := Crossing (G:=G) (pages:=P.copies) i
  have H := native_weight_multiplicity P i 2 1
  rw [modeWeight_fibre,if_pos (by decide : 0<(1:ℕ) ∧ 1<2)] at H
  have hW : Nat.card I*2^(i.val+1)≤6*Nat.card E :=
    (Nat.le_mul_of_pos_right _ (by positivity : 0<(2:ℕ)^(a-i.val))).trans H
  rw [full_roster_length ms hm hall]
  change Nat.card (I×Fin (2^(i.val+1))×Fin (p-1))≤_
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fin,Nat.card_fin,← mul_assoc]
  exact Nat.mul_le_mul hW (Nat.sub_le _ _)

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
include cfg

set_option exponentiation.threshold 12000 in
theorem register_size_bound
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (ha : (S).cutoff<c.edges) (t : Center S c) :
    registerPrecision S c t≤precisionSize s C := by
  let lam := Nat.clog 2 s
  let L := stepL lam c.depth
  let u := stepU lam c.depth
  let a := stepA lam c.depth
  obtain ⟨hu,_,_,hP⟩ := register_envelope cfg sel h hr hzero hroot ha t
  have hV : registerPrecision S c t≤registerPrecision S c t*u :=
    Nat.le_mul_of_pos_right _ hu
  have hL : L≤s := by
    have h0 : 0<L := by unfold L stepL; positivity
    have H := (dimensions_small s c.depth cfg.widthPos).1
    exact ((show L≤L^1000 from
      (pow_one L).symm.trans_le (Nat.pow_le_pow_right h0 (by decide))).trans H.le)
  have hD : 2^(a-padicValInt 2 t.val)≤s :=
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)).trans hL
  have hF := (stable_reachable cfg sel h hr).sizeByDepth
  have hM : c.edges≤C*s :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans hF
  exact hV.trans (hP.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hD))

theorem roster_size_bound
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (d : Ready S (sourceDelta s) c) (t : Center S c)
    (ms : List (NativeRoster sel d t)) (hm : ms.Nodup) (hall : ∀ m,m∈ms) :
    ms.length≤rosterSize s C := by
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have H := physical_roster_length (packing sel d) (centerIndex d t) ms hm hall
  have hE : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  rw [hE] at H
  have hF := (stable_reachable cfg sel h hr).sizeByDepth
  have hM : c.edges≤C*s :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans hF
  exact H.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM)
    (register_size_bound cfg sel h hr hzero hroot d.active t))

#print axioms localFee_mono
#print axioms raw_width_fits
#print axioms physical_roster_length
#print axioms register_size_bound
#print axioms roster_size_bound
end J6R16ModeCost



