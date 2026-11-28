import J6R18ChildWriteRow
import J6R18ChildWritePower

/-! Source powers share the same supplied column bit records but do
not read target bits. Exponents and row-count checks come from the
same raw beta words; masking a non-target writes an actual zero word. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open A1R10 A1R11 A1R12 J6R9PacketTiles

noncomputable def requestedProfile {a p q m : ℕ} {i : Fin a}
    (ms : Fin m→ModeInput a p i q) : Fin m→₀ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j=>if (ms j).targeted then (ms j).beta.val else 0)

theorem requestedProfile_read {a p q m : ℕ} {i : Fin a} (ms : Fin m→ModeInput a p i q)
    (j : Fin m) : requestedProfile ms j = if (ms j).targeted then (ms j).beta.val else 0 := by
  let f : Fin m→ℕ := fun j=>if (ms j).targeted then (ms j).beta.val else 0
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply f) j

def prepareCheck {a p q : ℕ} {i : Fin a} (m : ModeInput a p i q) : List Bool×List Bool :=
  (m.code, if m.targeted then m.beta.bits else encodeBits q 0)

def prepareChecks {a p q : ℕ} {i : Fin a} (b : ℕ) (ms : List (ModeInput a p i q)) :
    Meter (List (List Bool×List Bool)) :=
  A1R12.mapMeter (fun m=> ⟨prepareCheck m,2*b+4*q+8⟩) (b+q) ms

theorem prepareChecks_exact {a p q m : ℕ} {i : Fin a} (b : ℕ)
    (ms : Fin m→ModeInput a p i q) (hc : ∀ j,(ms j).code=encodeBits b j.succ.val) :
    let z := prepareChecks b (List.ofFn ms)
    z.result=A1R9.counterTape b q (requestedProfile ms) (List.finRange m) ∧
      z.steps≤m*((2*b+4*q+8)+(b+q)+4) := by
  have h := A1R12.mapMeter_exact (fun x : ModeInput a p i q=>⟨prepareCheck x,2*b+4*q+8⟩)
    (b+q) (2*b+4*q+8) (List.ofFn ms) (fun _ _=>le_rfl)
  obtain ⟨hV,hC⟩ := h
  constructor
  · unfold prepareChecks A1R9.counterTape
    rw [hV,List.ofFn_eq_map,List.map_map]
    apply List.map_congr_left
    intro j _
    change ((ms j).code,if (ms j).targeted then (ms j).beta.bits else encodeBits q 0)=_
    rw [requestedProfile_read,hc]
    by_cases e : (ms j).targeted=true
    · simp only [e,if_true]
      exact Prod.ext rfl (congrArg J6R15ModeCost.Word.bits (J6R15ModeCost.valued_word (ms j).beta)).symm
    · simp [e]
  · simpa only [List.length_ofFn] using hC

theorem profile_fits {a p q m : ℕ} {i : Fin a} (ms : Fin m→ModeInput a p i q) (j : Fin m) :
    requestedProfile ms j<2^q := by
  rw [requestedProfile_read]
  split
  · exact J6R15ModeCost.val_lt (ms j).beta
  · exact Nat.two_pow_pos q

noncomputable def sourceMoment {R : Type*} [CommRing R] {a : ℕ} (i : Fin a) (tau b : ℕ)
    (cols : List (SlotBit a)) : R :=
  (cols.map (fun x=>if tile i.val x.index.val=tau then (coord i.val x.index.val:R)^b * bit R x.assigned else 0)).sum

def momentWord {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a) (tau : J6R15ModeCost.Word (i.val+1)) (b : ℕ)
    (cols : List (SlotBit a)) : Meter (UVBlock fw ell) :=
  sumUV hp (fun x=>onTile hp he hv i x tau b) cols

def momentFee (a e ell p cols b : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+cols*(tileFee a e ell p b+addCap e ell p hp+2)

theorem momentWord_exact {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a) (tau : J6R15ModeCost.Word (i.val+1)) (b : ℕ)
    (cols : List (SlotBit a)) :
    let v := momentWord hp he hv i tau b cols
    uvRead hp fw ell v.result=sourceMoment i tau.val b cols ∧
      v.steps≤momentFee a fw.length ell p cols.length b hp :=
  sumUV_exact hp _ _ _ cols (fun x _=>onTile_exact hp he hv i x tau b)

noncomputable def sourcedValue {R : Type*} [CommRing R] {a p q : ℕ} {i : Fin a}
    (cols : List (SlotBit a)) (m : ModeInput a p i q) : R :=
  if m.sourced then (sourceMoment i m.tile.val m.order.val cols:R)^m.beta.val else 1

def sourcePower {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a)
    (cols : List (SlotBit a)) (m : ModeInput a p i q) : Meter (UVBlock fw ell) :=
  if m.sourced then
    let x := momentWord hp he hv i m.tile m.order.val cols
    let z := powBits hp he hv m.beta.bits x.result
    ⟨z.result,x.steps+z.steps+2*q+8⟩
  else oneM hp he hv

def sourcePowerFee (a e ell p q cols : ℕ) (hp : 0<p) : ℕ :=
  momentFee a e ell p cols p hp+powBitCap e ell p q+uvWidth e ell p+2*q+8

theorem sourcePower_exact {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a) (cols : List (SlotBit a)) (m : ModeInput a p i q) :
    let w := sourcePower hp he hv i cols m
    uvRead hp fw ell w.result=sourcedValue cols m ∧
      w.steps≤sourcePowerFee a fw.length ell p q cols.length hp := by
  by_cases hs : m.sourced=true
  · let x := momentWord hp he hv i m.tile m.order.val cols
    let z := powBits hp he hv m.beta.bits x.result
    obtain ⟨hX,cX⟩ := momentWord_exact hp he hv i m.tile m.order.val cols
    obtain ⟨hZ,cZ⟩ := powBits_exact hp he hv m.beta.bits x.result
    have hM : momentFee a fw.length ell p cols.length m.order.val hp≤momentFee a fw.length ell p cols.length p hp := by
      have : m.order.val≤p := by have := m.order.isLt; omega
      unfold momentFee tileFee
      gcongr
    change z.steps≤_ at cZ
    rw [m.beta.size] at cZ
    have hLX : x.steps≤momentFee a fw.length ell p cols.length p hp := cX.trans hM
    unfold sourcePower sourcedValue
    rw [if_pos hs,if_pos hs]
    refine ⟨by rw [show uvRead hp fw ell z.result=_ from hZ,hX]; rfl,?_⟩
    change x.steps+z.steps+2*q+8≤_
    unfold sourcePowerFee
    omega
  · unfold sourcePower sourcedValue
    rw [if_neg hs,if_neg hs]
    refine ⟨oneM_read hp he hv,?_⟩
    change uvWidth fw.length ell p≤_
    unfold sourcePowerFee
    omega

def sourceProduct {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a)
    (cols : List (SlotBit a)) (modes : List (ModeInput a p i q)) : Meter (UVBlock fw ell) :=
  foldM hp he hv (sourcePower hp he hv i cols) modes

theorem sourceProduct_exact {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a) (cols : List (SlotBit a)) (modes : List (ModeInput a p i q)) :
    let z := sourceProduct hp he hv i cols modes
    uvRead hp fw ell z.result=(modes.map (sourcedValue cols)).prod ∧
      z.steps≤uvWidth fw.length ell p+
        modes.length*(sourcePowerFee a fw.length ell p q cols.length hp+mulCap fw.length ell p+2) :=
  foldM_exact hp he hv modes _ _ _ (fun m _=>sourcePower_exact hp he hv i cols m)

#print axioms prepareChecks_exact
#print axioms momentWord_exact
#print axioms sourcePower_exact
#print axioms sourceProduct_exact
end J6R18ChildWrite

