import J6R16ModeCostEnvelope
import J6R16ModeCostGeometric
import J6R16ModeCostCatalog

/-! On a reachable ready call, the exact roster bound and the
paid R15 stream use the same registerPrecision and the same exponent
envelope. A tape is supplied, not constructed in this module. -/
namespace J6R16ModeCost
open scoped Polynomial BigOperators Classical
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint
open J6R11Blueprint J6R15ModeCost

def branchBits (lam : ℕ) : ℕ := 5*lam+7

def setupCap (q n : ℕ) : ℕ := 16*q+14+4*(n+1)*(q+1)

def localFeeCap (q n : ℕ) : ℕ := setupCap q n+2*delayCap q n

theorem fee_times_depth (li q n e : ℕ) (h : li≤2^e) :
    setupCap q n+(li+1)*delayCap q n≤localFeeCap q n*2^e := by
  have hp : 1≤(2:ℕ)^e := Nat.succ_le_of_lt (by positivity)
  have hM : li+1≤2*(2:ℕ)^e := by omega
  unfold localFeeCap
  calc
    _≤setupCap q n*2^e+(2*(2:ℕ)^e)*delayCap q n :=
      Nat.add_le_add (Nat.le_mul_of_pos_right _ hp) (Nat.mul_le_mul_right _ hM)
    _=_ := by ring

theorem signed_grid_count (a : ℕ) : (P1DyadicGrid.grid a).card=2^(a+1) := by
  rw [P1DyadicGrid.grid,Int.card_Ico,P1DyadicGrid.pow₂,pow_succ]
  have h : (0:ℤ)≤(2:ℤ)^a := by positivity
  rw [sub_neg_eq_add,Int.toNat_add h h]
  have he : (2:ℤ)^a=↑((2:ℕ)^a) := (Int.natCast_pow 2 a).symm
  rw [he,Int.toNat_natCast]
  omega

theorem centers_le {Host M : Type*} (S : Shape Host M) (c : Call Host) :
    Nat.card (Center S c)≤2^(S.levelBits c.depth+1) := by
  let a := S.levelBits c.depth
  change Nat.card ↑(active a c.edges (S.levelWidth c.depth))≤_
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,← signed_grid_count]
  apply Finset.card_le_card
  intro t ht
  exact (J6R9Recursive.active_grid _ _ _ ht).1

theorem nat_card_sigma_bound {A : Type*} [Fintype A] {B : A→Type*} [∀ a,Fintype (B a)]
    (K : ℕ) (H : ∀ a,Nat.card (B a)≤K) : Nat.card (Σ a,B a)≤Nat.card A*K := by
  rw [Nat.card_eq_fintype_card (α:=Σ a,B a),Fintype.card_sigma,Nat.card_eq_fintype_card (α:=A)]
  have h : (∑ a : A,Fintype.card (B a))≤∑ _ : A,K :=
    Finset.sum_le_sum (fun a _ => by simpa only [Nat.card_eq_fintype_card] using H a)
  simpa using h

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

include cfg

theorem tuple_depth_bound
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (d : Ready S (sourceDelta s) c) (t : Center S c)
    (ms : List (NativeRoster sel d t)) (hn : ms.Nodup) (hall : ∀ m,m∈ms) :
    (strictTuples (ms.map modeWeight) (registerPrecision S c t)).length≤
      2^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let lam := Nat.clog 2 s
  let u := stepU lam c.depth
  let p := registerPrecision S c t
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hM : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  obtain ⟨hu,hp,h6,hP⟩ := register_envelope cfg sel h hr hzero hroot d.active t
  have h6' : 6*Nat.card c.host.Edge≤p := by rwa [hM]
  have hP' : p*u≤siteConstant C*Nat.card c.host.Edge*2^(stepA lam c.depth-(centerIndex d t).val) := by
    rw [hM]
    exact hP
  have hT := native_schedule_bound (packing sel d) (centerIndex d t) ms hn hall hp h6' u (siteConstant C) hu hP'
  rw [hM] at hT
  refine hT.trans (Nat.pow_le_pow_right (by decide) ?_)
  have hsize := (stable_reachable cfg sel h hr).sizeByDepth
  have hL : 0<lam := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  exact Nat.mul_le_mul_left 18
    (depth_sqrt_le s C lam (siteConstant C) c.depth c.edges u hL hu (floor_scale lam c.depth hu) hsize)

theorem native_menu_depth_bound
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (d : Ready S (sourceDelta s) c) (t : Center S c) :
    Nat.card (NativeMenu (N sel) c t)≤2^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let ms := (Finset.univ : Finset (NativeRoster sel d t)).toList
  have hn : ms.Nodup := Finset.nodup_toList _
  have hall (m : NativeRoster sel d t) : m∈ms := by simp [ms]
  exact (site_menu_count sel d t ms hn hall).trans
    (tuple_depth_bound cfg sel h hr hzero hroot d t ms hn hall)

theorem live_addresses_bound
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0) (hroot : r.prec≤C*s) :
    Nat.card ((Plan sel).Slot c)≤
      2^(branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let lam := Nat.clog 2 s
  let E := depthExponent s C lam (siteConstant C) c.depth
  by_cases ha : (S).cutoff<c.edges
  · let d := ready_reachable cfg sel h hr ha
    letI := nativeAddressFintype (N sel) c
    have hInj : Nat.card ((Plan sel).Slot c)≤Nat.card (NativeAddress (N sel) c) :=
      Nat.card_le_card_of_injective (fun a : (Plan sel).Slot c => (a.val : NativeAddress (N sel) c))
        Subtype.val_injective
    have hCtr : Nat.card (Center S c)≤2^(lam+1) :=
      (centers_le S c).trans (Nat.pow_le_pow_right (by decide)
        (Nat.succ_le_succ (bits_le_lam lam c.depth)))
    have hProbe : Nat.card (Probe S c)≤2^(4*lam) := by
      have H := d.fit
      change J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)≤2^f.natDegree at H
      rw [cfg.coefficient] at H
      rwa [Nat.card_fin]
    rw [Nat.card_fin] at hProbe
    letI : ∀ t : Center S c, Fintype (NativeMenu (N sel) c t) :=
      fun t => Finset.fintypeCoeSort (@J6RecursiveMenu.menu ((N sel).Mode c t)
        ((N sel).finiteMode c t) ((N sel).decideMode c t)
        (registerPrecision S c t) ((N sel).weight c t))
    apply hInj.trans
    have hbound (t : Center S c) :
        Nat.card (Probe S c×NativeMenu (N sel) c t×Fin 64)≤2^(4*lam)*(2^E*64) := by
      simp only [Nat.card_prod,Nat.card_fin]
      exact Nat.mul_le_mul hProbe (Nat.mul_le_mul_right _ (native_menu_depth_bound cfg sel h hr hzero hroot d t))
    refine (nat_card_sigma_bound _ hbound).trans ?_
    calc
      _≤2^(lam+1)*(2^(4*lam)*(2^E*64)) := Nat.mul_le_mul_right _ hCtr
      _=2^(branchBits lam+E) := by
        rw [show (64:ℕ)=2^6 by decide,← pow_add,← pow_add,← pow_add]
        congr 1
        unfold branchBits
        omega
  · letI : IsEmpty ((Plan sel).Slot c) := ⟨fun a => ha a.property⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

#print axioms signed_grid_count
#print axioms centers_le
#print axioms tuple_depth_bound
#print axioms native_menu_depth_bound
#print axioms live_addresses_bound
end J6R16ModeCost




