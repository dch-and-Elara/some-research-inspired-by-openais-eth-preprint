import J6R62ActivePrepSite
import J6R17ModeTapeReach
import J6R57ActiveFeeFixed

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 2180
set_option Elab.async false

/-! Polynomial fee for the pre-dispatch tape at the actual active
path. Unlike the historical R17 global fold, this bound never resets
the root's absolute depth or presupposes a chosen outgoing slot. -/
namespace J6R62ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime
open J6R14LayoutCost J6R17ModeTape J6R31RootResidentTables
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R50Peak J6R57ActiveFee J6R49DFS J6R9Recursive

def headerPolynomial (K : ℕ) : ℕ :=
  16*(6*K+1)*K+K*((8*(6*K)+22)*K+4)+4+(206*K+6+18)*K+4

def tapePolynomial (K : ℕ) : ℕ :=
  headerPolynomial K+2*(3*K+1)+buildCap K K K 0 0 K K K+4

theorem canonical_cap_of_small_dimensions {a q i b p K : ℕ}
    (width : a≤K) (word : q≤K) (headers : 2^(6*a)*2^(6*a)≤K)
    (copies : b≤K) (tiles : 2^(i+1)≤K) (precision : p≤K) :
    canonicalCap a q i b p≤tapePolynomial K := by
  have single : 2^(6*a)≤K :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans headers
  have hH : headerBankFee a≤headerPolynomial K := by
    unfold headerBankFee allPairsCap headerCap headerPolynomial
    gcongr
  have hB : buildCap a q (2^(6*a)*2^(6*a)) 0 0 b (2^(i+1)) p≤
      buildCap K K K 0 0 K K K := by
    calc
      _≤buildCap a q K 0 0 K K K :=
        buildCap_mono a q headers le_rfl le_rfl copies tiles precision
      _≤buildCap K q K 0 0 K K K := buildCap_dim a K q K 0 0 K K K width
      _≤_ := by
        unfold buildCap headerTraffic keyCap pageCap tileCap layerCap weightCap recordStride spanFee
        gcongr
  unfold canonicalCap tapePolynomial
  gcongr

noncomputable section
variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

abbrev readyAtPath (T : Prepared cfg sel r hf) (p : Path sel r c)
    (on : (S).cutoff<c.edges) :
    Ready S (sourceDelta s) c :=
  ready_reachable cfg sel p.reached T.rootStable on

theorem paid_tape_at_actual_path
    (T : Prepared cfg sel r hf) (p : Path sel r c)
    (on : (S).cutoff<c.edges) (t : Center S c)
    (hq : 0<q) (axisFits : (centerIndex (readyAtPath T p on) t).val+1<q)
    (input : Meter (CentreWords sel (readyAtPath T p on) t q))
    (K : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) :
    (paidTape hq axisFits input).steps ≤ input.steps+tapePolynomial K := by
  let d := readyAtPath T p on
  obtain ⟨a,headers,_,copies,tiles⟩ :=
    native_layout_sizes cfg sel p.reached T.rootStable d t
  have edges : C*s≤K := (Nat.le_mul_of_pos_left (C*s) (by decide : 0<(4:ℕ))).trans cs.edges
  have scale : s≤K := (Nat.le_mul_of_pos_left s cfg.constPos).trans edges
  have pFit : registerPrecision S c t≤K :=
    (absolute_register_precision_cap cfg sel T.rootStable p on t).trans ws.register
  have copyFit : (packing sel d).copies≤K :=
    copies.trans ((Nat.mul_le_mul_right (C*s) (by decide : (3:ℕ)≤4)).trans cs.edges)
  have bound := canonical_cap_of_small_dimensions (a.trans scale) ws.modeWord
    (headers.trans edges) copyFit (tiles.trans scale) pFit
  exact (paid_tape_local_fee hq axisFits input).2.trans (Nat.add_le_add_left bound _)

/-- One legitimate global word-width choice. The proof depends on the
actual centre's axis, not the depth of this run's outer root. -/
theorem uniform_width_fits_before_dispatch
    (T : Prepared cfg sel r hf) (p : Path sel r c)
    (on : (S).cutoff<c.edges) (t : Center S c) :
    (centerIndex (readyAtPath T p on) t).val+1<J6R16ModeCost.uniformWidth s C :=
  site_input_width cfg (readyAtPath T p on) t

/-- The replaced coordinate roster can be processed by the same
typed child callback with no numerical change, even if the legacy
typed tape chose a different order. The complete list below is a
common proof-side comparison, never a run-time catalogue. -/
theorem mounted_tape_keeps_typed_centre_value
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
    {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}
    (J : CentreMachine sel d t bank q)
    (hq : 0<q) (axisFits : (centerIndex d t).val+1<q)
    (input : Meter (CentreWords sel d t q))
    {pHigh : ℕ} (hv : 0<ell) (hf : f.Monic) (H : Frame f pHigh) (B : ℕ)
    (read : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    ((mountAtCentre J hq axisFits input).runCentre hq hv hf H B read).result=
      (J.runCentre hq hv hf H B read).result := by
  classical
  letI : Fintype (NativeMenu (N sel) c t) := nativeMenuFinite (N sel) c t
  let L := (Finset.univ : Finset (NativeMenu (N sel) c t)).toList
  have nd : L.Nodup := Finset.nodup_toList _
  have complete : ∀ x,x∈L := by intro x; simp [L]
  have left := centre_stream_value (mountAtCentre J hq axisFits input) hq hv hf H B read L nd complete
  have right := centre_stream_value J hq hv hf H B read L nd complete
  exact left.trans right.symm

#print axioms mounted_tape_keeps_typed_centre_value

#print axioms canonical_cap_of_small_dimensions
#print axioms paid_tape_at_actual_path
#print axioms uniform_width_fits_before_dispatch
end
end J6R62ActivePrep

