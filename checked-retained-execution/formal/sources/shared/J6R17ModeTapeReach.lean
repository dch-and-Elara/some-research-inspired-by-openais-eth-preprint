import J6R17ModeTapeSite
import J6R14LayoutCostPoly

/-! Explicit polynomial tariff for building the address/weight tape
at any genuinely reachable active Appendix D site. -/
namespace J6R17ModeTape
open scoped Classical Polynomial BigOperators
open AOracleMachineTime J6ActiveRun J6R12Blueprint J6R10Reachable J6R11Blueprint
open J6R16ModeCost J6R15ModeCost J6R10Repack J1PPrinted J6R14LayoutCost

def buildUniform (s C : ℕ) : ℕ :=
  let q := uniformWidth s C
  buildCap s q (C*s) (C*s) (rowTraffic q q (6*s) q s) (3*(C*s)) s (precisionSize s C)

theorem buildCap_dim (a A q n m w b t p : ℕ) (ha : a≤A) :
    buildCap a q n m w b t p≤buildCap A q n m w b t p := by
  unfold buildCap headerTraffic keyCap pageCap tileCap layerCap recordStride weightCap
  gcongr
  unfold recordStride
  omega

theorem traffic_bound (a s q kR kC : ℕ) (ha : a≤s) (hr : kR≤q) (hc : kC≤q) :
    rowTraffic kR kC (6*a) q a≤rowTraffic q q (6*s) q s := by
  unfold rowTraffic
  gcongr

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {r c : Call (PhysicalHost f ell)}
include cfg

set_option exponentiation.threshold 11000 in
theorem dimension_size (c : Call (PhysicalHost f ell)) :
    2^(S).levelBits c.depth≤s := by
  let L := stepL (Nat.clog 2 s) c.depth
  change L≤s
  have hL : 0<L := by unfold L stepL; positivity
  exact ((pow_one L).symm.trans_le (Nat.pow_le_pow_right hL (by decide : 1≤1000))).trans
    (dimensions_small s c.depth cfg.widthPos).1.le

theorem site_input_width (d : Ready S (sourceDelta s) c) (t : Center S c) :
    (centerIndex d t).val+1<uniformWidth s C := by
  let a := (S).levelBits c.depth
  have hA : a+1≤s :=
    (J9PrintedSchedule.next_le_two_power a).trans (dimension_size (ell:=ell) cfg c)
  have hC : s≤C*s := Nat.le_mul_of_pos_left _ cfg.constPos
  have hK : C*s≤precisionSize s C := by
    have hs : 0<s := cfg.constPos.trans_le cfg.constSmall
    exact (Nat.le_mul_of_pos_left (C*s) (by unfold siteConstant; omega)).trans
      (Nat.le_mul_of_pos_right _ hs)
  have hi := (centerIndex d t).isLt
  unfold uniformWidth
  omega

theorem native_layout_sizes (h : NativeReach (Plan sel) r c) (hr : Stable s C r)
    (d : Ready S (sourceDelta s) c) (t : Center S c) :
    let a := (S).levelBits c.depth
    a≤s ∧ 2^(6*a)*2^(6*a)≤C*s ∧ c.edges≤C*s ∧
      (packing sel d).copies≤3*(C*s) ∧ 2^((centerIndex d t).val+1)≤s := by
  let a := (S).levelBits c.depth
  have hL := dimension_size cfg c
  have hA : a≤s := (Nat.le_succ a).trans ((J9PrintedSchedule.next_le_two_power a).trans hL)
  have hE : c.edges≤C*s :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans
      (stable_reachable cfg sel h hr).sizeByDepth
  have hQ : 2^(6*a)*2^(6*a)≤C*s :=
    (source_menu_fit a (6*a) c.edges rfl d.paddedSlots).trans hE
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hN : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  let P := packing sel d
  have hB := P.paddedBudget
  rw [hN,P11FullPacking.total_cells,Fintype.card_fin] at hB
  have hP : P.copies≤3*(C*s) := by
    apply le_trans _ (hB.trans (Nat.mul_le_mul_left 3 hE))
    exact (Nat.le_mul_of_pos_right _ (by positivity : 0<(2:ℕ)^a)).trans
      (Nat.le_mul_of_pos_left _ (by positivity : 0<(64:ℕ)^(2*a)))
  have hi : (centerIndex d t).val+1≤a := (centerIndex d t).isLt
  exact ⟨hA,hQ,hE,hP,(Nat.pow_le_pow_right (by decide) hi).trans hL⟩

def rawSite (d : Ready S (sourceDelta s) c) (t : Center S c) (L : CallLayout (C:=C) sel d) :
    Meter (RawTape (uniformWidth s C)) :=
  let a := (S).levelBits c.depth
  buildTape (by unfold uniformWidth; omega) a (centerIndex d t).val
    (rowTraffic L.leftWidth L.rightWidth (6*a) (uniformWidth s C) a)
      L.layout.boxes L.layout.copies (L.precision t)

theorem raw_site_bound (h : NativeReach (Plan sel) r c) (hr : Stable s C r)
    (hzero : r.depth=0) (hroot : r.prec≤C*s) (d : Ready S (sourceDelta s) c)
    (t : Center S c) (L : CallLayout (C:=C) sel d) :
    let z := rawSite sel d t L
    ∃ I : SiteTape sel d t (uniformWidth s C),
      z.result.modes=I.modes.map (encodeMode (centerIndex d t)) ∧ z.result.modes.Nodup ∧
      z.result.weights=I.words ∧ z.result.precision=I.precision ∧ z.steps≤buildUniform s C := by
  let a := (S).levelBits c.depth
  let q := uniformWidth s C
  let tr := rowTraffic L.leftWidth L.rightWidth (6*a) q a
  have hq : 0<q := by unfold q uniformWidth; omega
  obtain ⟨hA,hD,hM,hB,hT⟩ := native_layout_sizes cfg sel h hr d t
  have hP := register_size_bound cfg sel h hr hzero hroot d.active t
  have hTr := traffic_bound a s q L.leftWidth L.rightWidth hA L.leftFit L.rightFit
  obtain ⟨I,hEnc,hDup,hW,hE,hC⟩ :=
    siteTape_from_layout sel hq d t (site_input_width cfg d t) tr L.layout (L.precision t) (L.exactPrecision t)
  refine ⟨I,hEnc,hDup,hW,hE,hC.trans ?_⟩
  calc
    _≤buildCap a q (C*s) (C*s) (rowTraffic q q (6*s) q s) (3*(C*s)) s (precisionSize s C) :=
      buildCap_mono a q hD hM hTr hB hT hP
    _≤buildUniform s C := buildCap_dim a s q _ _ _ _ _ _ hA

#print axioms dimension_size
#print axioms site_input_width
#print axioms native_layout_sizes
#print axioms raw_site_bound
end J6R17ModeTape

