import J6R68AbsolutePrescribedSeed
import J6R32StatefulArithmeticPath

/-! R16's exact branching bound from the invariant already proved at
the prescribed zero child. No native predecessor for that step is
fabricated. The native suffix and absolute depth are unchanged. -/
namespace J6R68AbsolutePrescribed
open scoped Polynomial BigOperators Classical
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R15ModeCost J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4100
set_option Elab.async false
set_option quotPrecheck false

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
include cfg

theorem absolute_seed_register_envelope (seed : AbsoluteSeed s C c)
    (ha : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c) :
    let lam := Nat.clog 2 s
    let u := stepU lam c.depth
    let a := stepA lam c.depth
    let D := 2^(a-padicValInt 2 t.val)
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
    0<u ∧ 0<p ∧ 6*c.edges ≤ p ∧ p*u ≤ siteConstant C*c.edges*D := by
  let lam := Nat.clog 2 s
  let u := stepU lam c.depth
  let a := stepA lam c.depth
  let i := padicValInt 2 t.val
  let D := (2:ℕ)^(a-i)
  have hSt := seed.stable
  have hp0 : 0<lam := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  obtain ⟨hu,_,huM⟩ :=
    printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size ha hSt.sizeByDepth
  have hi : i<u := center_level a c.edges u t.property
  obtain ⟨hD,hlD,_⟩ := scale_at_center lam c.depth i hi
  have hp5 := printed_u_four_fifths s c.edges C c.depth cfg.constPos cfg.size ha hSt.sizeByDepth
  have hdom := dominant_dyadic lam u (root_lambda_large cfg) hp5
  have hs : s ≤ c.edges*(lam+1) :=
    (cutoff_scale s lam c.edges hp0 ha).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have hul : u ≤ lam+1 := (u_le_lam lam c.depth).trans (Nat.le_succ _)
  have hal : a+1 ≤ lam+1 := Nat.succ_le_succ (bits_le_lam lam c.depth)
  have hPrec := absolute_seed_input_precision_poly cfg seed
  have hInherited : c.prec*u ≤ 41*C*c.edges*D := by
    calc
      _ ≤ (41*C*s*(lam+1)^2*2^priorBits lam c.depth)*u :=
        Nat.mul_le_mul_right _ hPrec
      _=(41*C)*(lam+1)^2*2^priorBits lam c.depth*(s*u) := by ring
      _ ≤ (41*C)*(lam+1)^2*2^priorBits lam c.depth*((c.edges*(lam+1))*(lam+1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hs hul)
      _=(41*C*c.edges)*((lam+1)^4*2^priorBits lam c.depth) := by ring
      _ ≤ (41*C*c.edges)*((2:ℕ)^u*2^priorBits lam c.depth) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdom)
      _=(41*C*c.edges)*2^(priorBits lam c.depth+u) := by rw [pow_add,mul_comm (2^u)]
      _ ≤ _ := Nat.mul_le_mul_left _ hlD
  have hGeometry : u*(a+1) ≤ D := by
    calc
      _ ≤ (lam+1)*(lam+1) := Nat.mul_le_mul hul hal
      _=(lam+1)^2 := (pow_two _).symm
      _ ≤ (lam+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ 2^u := hdom
      _ ≤ 2^(priorBits lam c.depth+u) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := hlD
  let H := height c.edges u
  have hHu : H*u ≤ 4*c.edges := (height_bounds c.edges u hu huM).2
  have hE : 0<c.edges := Nat.zero_lt_of_lt ha
  have hD' : (2:ℕ)^a/2^i=D := hD
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
  have hp : p=c.prec+8*H*D+8*c.edges*(a+1) := by
    change c.prec+8*H*(2^a/2^i)+8*c.edges*(a+1)=_
    rw [hD']
  have hlower : 6*c.edges ≤ p := by
    have ht : 8*c.edges ≤ 8*c.edges*(a+1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [hp]
    omega
  refine ⟨hu,?_,hlower,?_⟩
  · omega
  · change p*u ≤ siteConstant C*c.edges*D
    rw [hp]
    calc
      _=c.prec*u+(8*D)*(H*u)+(8*c.edges)*(u*(a+1)) := by ring
      _ ≤ 41*C*c.edges*D+(8*D)*(4*c.edges)+(8*c.edges)*D :=
        Nat.add_le_add (Nat.add_le_add hInherited (Nat.mul_le_mul_left _ hHu))
          (Nat.mul_le_mul_left _ hGeometry)
      _=_ := by unfold siteConstant; ring

theorem absolute_seed_tuple_depth_bound
    (seed : AbsoluteSeed s C c)
    (d : Ready S (sourceDelta s) c) (t : Center S c)
    (ms : List (NativeRoster sel d t)) (hn : ms.Nodup) (hall : ∀ m,m∈ms) :
    (strictTuples (ms.map modeWeight) (registerPrecision S c t)).length ≤ 2^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let lam := Nat.clog 2 s
  let u := stepU lam c.depth
  let p := registerPrecision S c t
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hM : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  obtain ⟨hu,hp,h6,hP⟩ := absolute_seed_register_envelope cfg seed d.active t
  have h6' : 6*Nat.card c.host.Edge ≤ p := by rwa [hM]
  have hP' : p*u ≤ siteConstant C*Nat.card c.host.Edge*2^(stepA lam c.depth-(centerIndex d t).val) := by
    rw [hM]
    exact hP
  have hT := native_schedule_bound (packing sel d) (centerIndex d t) ms hn hall hp h6' u (siteConstant C) hu hP'
  rw [hM] at hT
  refine hT.trans (Nat.pow_le_pow_right (by decide) ?_)
  have hsize := (seed.stable).sizeByDepth
  have hL : 0<lam := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  exact Nat.mul_le_mul_left 18
    (depth_sqrt_le s C lam (siteConstant C) c.depth c.edges u hL hu (floor_scale lam c.depth hu) hsize)

theorem absolute_seed_menu_depth_bound
    (seed : AbsoluteSeed s C c)
    (d : Ready S (sourceDelta s) c) (t : Center S c) :
    Nat.card (NativeMenu (N sel) c t) ≤ 2^(depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let ms := (Finset.univ : Finset (NativeRoster sel d t)).toList
  have hn : ms.Nodup := Finset.nodup_toList _
  have hall (m : NativeRoster sel d t) : m∈ms := by simp [ms]
  exact (site_menu_count sel d t ms hn hall).trans
    (absolute_seed_tuple_depth_bound cfg sel seed d t ms hn hall)

theorem absolute_seed_live_addresses_bound
    (seed : AbsoluteSeed s C c) :
    Nat.card ((Plan sel).Slot c) ≤ 2^(branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) := by
  let lam := Nat.clog 2 s
  let E := depthExponent s C lam (siteConstant C) c.depth
  by_cases ha : (S).cutoff<c.edges
  · let d := getReady cfg seed.stable ha
    letI := nativeAddressFintype (N sel) c
    have hInj : Nat.card ((Plan sel).Slot c) ≤ Nat.card (NativeAddress (N sel) c) :=
      Nat.card_le_card_of_injective (fun a : (Plan sel).Slot c => (a.val : NativeAddress (N sel) c))
        Subtype.val_injective
    have hCtr : Nat.card (Center S c) ≤ 2^(lam+1) :=
      (centers_le S c).trans (Nat.pow_le_pow_right (by decide)
        (Nat.succ_le_succ (bits_le_lam lam c.depth)))
    have hProbe : Nat.card (Probe S c) ≤ 2^(4*lam) := by
      have H := d.fit
      change J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth) ≤ 2^f.natDegree at H
      rw [cfg.coefficient] at H
      rwa [Nat.card_fin]
    rw [Nat.card_fin] at hProbe
    letI : ∀ t : Center S c, Fintype (NativeMenu (N sel) c t) :=
      fun t => Finset.fintypeCoeSort (@J6RecursiveMenu.menu ((N sel).Mode c t)
        ((N sel).finiteMode c t) ((N sel).decideMode c t)
        (registerPrecision S c t) ((N sel).weight c t))
    apply hInj.trans
    have hbound (t : Center S c) :
        Nat.card (Probe S c×NativeMenu (N sel) c t×Fin 64) ≤ 2^(4*lam)*(2^E*64) := by
      simp only [Nat.card_prod,Nat.card_fin]
      exact Nat.mul_le_mul hProbe (Nat.mul_le_mul_right _ (absolute_seed_menu_depth_bound cfg sel seed d t))
    refine (nat_card_sigma_bound _ hbound).trans ?_
    calc
      _ ≤ 2^(lam+1)*(2^(4*lam)*(2^E*64)) := Nat.mul_le_mul_right _ hCtr
      _=2^(branchBits lam+E) := by
        rw [show (64:ℕ)=2^6 by decide,← pow_add,← pow_add,← pow_add]
        congr 1
        unfold branchBits
        omega
  · letI : IsEmpty ((Plan sel).Slot c) := ⟨fun a => ha a.property⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

theorem actual_suffix_addresses_from_prescribed_seed (seed : AbsoluteSeed s C r)
    (p : Path sel r c) :
    Nat.card ((Plan sel).Slot c) ≤ 2^(branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) c.depth) :=
  absolute_seed_live_addresses_bound cfg sel (absolute_rail_reaches_suffix cfg sel seed p.reached)

#print axioms absolute_seed_register_envelope
#print axioms absolute_seed_tuple_depth_bound
#print axioms absolute_seed_menu_depth_bound
#print axioms absolute_seed_live_addresses_bound
#print axioms actual_suffix_addresses_from_prescribed_seed
end J6R68AbsolutePrescribed
