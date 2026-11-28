import V8NativeMessageN4RawPrecision
import V8NativeMessageC3HermiteReadout
import HermiteLossReceive
import V8PooledMenuGrid

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! The ordinary flattened D weight at an actual D1 probe: integral
decoder-basis lifts multiplied by the original signed-center Hermite
weights. No extra mode or group factor is charged this loss. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive J6ActiveRun J6ActiveSchedule
open Paper5.HybridClosure Paper5.D1Literal J6R12Blueprint J1PPrinted V8PooledMenu
open V8NativeMessage.C3.Hermite V8NativeMessage.C3.Canonical
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}

local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "r*" => oldRowRoot F reg f (fun _=>false)

def ordinaryDLoss (t : PublicCenter F reg f) : ℕ :=
  6*height (24*Fintype.card W) (widthU F)*nodeScale t+
    4*(24*Fintype.card W)*(2*widthU F+1)

theorem actual_height_guards (d : LayoutReady F reg f) (t : PublicCenter F reg f) :
    0<widthU F ∧ widthU F≤24*Fintype.card W := by
  let u := widthU F
  let a := (S).levelBits 0
  have he : Fintype.card (DWire F)=24*Fintype.card W := d_physical_wire_count F reg
  have h₁ : 0<order (Fintype.card (DWire F)) u t.val := active_order_pos _ _ _ _ t.property
  have hu : 0<u := by
    by_contra! hz
    have hu₀ : u=0 := by omega
    rw [hu₀,order,Nat.zero_sub,mul_zero] at h₁
    exact (lt_irrefl _ h₁)
  have hua : u≤a := d.widthFits
  have hslots : 2^a*J9PrintedSchedule.arrayCard a≤Fintype.card (DWire F) := d.paddedSlots
  have hbase : a≤(2:ℕ)^a := (show a<(2:ℕ)^a from Nat.lt_two_pow_self).le
  have hmul : (2:ℕ)^a≤2^a*J9PrintedSchedule.arrayCard a := by
    apply Nat.le_mul_of_pos_right
    unfold J9PrintedSchedule.arrayCard
    positivity
  rw [he] at hslots
  exact ⟨hu,hua.trans (hbase.trans (hmul.trans hslots))⟩

theorem source_stencil_loss (d : LayoutReady F reg f) (t : PublicCenter F reg f)
    (j : Orders S r* t) :
    HasLoss f 1 (ordinaryDLoss t) (originWeight S f 1 r* t j) := by
  let M := 24*Fintype.card W
  let u := widthU F
  let a := 2*u
  let h := height M u
  let τ : ℤ := t.val
  let k : ℕ := j.val
  have ae : (S).levelBits 0=a := width_precisionBits (F:=F) (f:=f)
  have he : (r*).edges=M := d_physical_wire_count F reg
  have hu : (S).levelWidth 0=u := rfl
  have hp : τ∈active a M u := by
    have ht : τ∈active ((S).levelBits 0) (r*).edges ((S).levelWidth 0) := t.property
    rwa [ae,he,hu] at ht
  obtain ⟨hg,hn⟩ := active_grid a M u hp
  obtain ⟨hu₀,huM⟩ := actual_height_guards d t
  have hj : j.val≤4*M := by
    have h' : k<order (r*).edges ((S).levelWidth 0) τ := j.isLt
    rw [he,hu] at h'
    exact h'.le.trans (order_bound M u t.val hu₀ huM)
  have hl := HermiteLoss.level_grid_le hg hn
  have hD : nodeScale t=2^(a-HermiteLoss.level t.val) := dyadic_div_pow hl
  let loss := HermiteLoss.totalLoss a h j.val t.val
  let B := ordinaryDLoss t
  have hloss : loss≤B := by
    change 6*h*2^(a-HermiteLoss.level t.val)+j.val*(a+1-HermiteLoss.level t.val)≤_
    change _≤6*h*nodeScale t+4*M*(a+1)
    rw [hD]
    exact Nat.add_le_add_left (Nat.mul_le_mul hj (Nat.sub_le _ _)) _
  let w := HermiteLoss.weight a u h k τ
  have hlocal : (2:ℚ)^loss*w∈twoLocalSubalgebra :=
    HermiteLoss.weight_scaled_integral a u h j.val hg hn
  have hlocal' : (2:ℚ)^B*w∈twoLocalSubalgebra := by
    have eqv : (2:ℚ)^B*w=(2:ℚ)^(B-loss)*((2:ℚ)^loss*w) := by
      rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hloss]
    rw [eqv]
    exact twoLocalSubalgebra.mul_mem (two_pow_local _) hlocal
  let W0 : TwoLocal := ⟨(2:ℚ)^B*w,hlocal'⟩
  refine ⟨localScalar f 1 W0,?_⟩
  rw [embed_localScalar]
  have hw : originWeight S f 1 r* t j = algebraMap ℚ (RatRing f 1) w := by
    change algebraMap ℚ (RatRing f 1)
      (HermiteLoss.weight ((S).levelBits 0) ((S).levelWidth 0)
        (HermiteLoss.sourceH (r*).edges ((S).levelWidth 0)) k τ)=_
    rw [ae,hu,he]
    rfl
  rw [hw]
  change (2:RatRing f 1)^B*algebraMap ℚ (RatRing f 1) w =
    algebraMap ℚ (RatRing f 1) ((2:ℚ)^B*w)
  rw [map_mul,map_pow,map_ofNat]

theorem literal_D_probe_loss (d : LayoutReady F reg f) (t : PublicCenter F reg f)
    (z : PublicProbe F reg f) :
    HasLoss f 1 (ordinaryDLoss t) (publicMenuWeight F reg f d t z) := by
  let p := registerPrecision S r* t
  let read := receivingDecoder S f 1 r* d.fit t (normalAt S f 1 r* t)
  choose a ha using fun j => source_stencil_loss d t j
  refine ⟨∑ j, a j * representative p f 1 (read (probeBasis z) j),?_⟩
  change (2:RatRing f 1)^ordinaryDLoss t*
    (∑ j, originWeight S f 1 r* t j * embed f 1 (representative p f 1 (read (probeBasis z) j))) =
    embed f 1 (∑ j, a j * representative p f 1 (read (probeBasis z) j))
  rw [Finset.mul_sum,map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← mul_assoc,ha j,map_mul])

#print axioms actual_height_guards
#print axioms source_stencil_loss
#print axioms literal_D_probe_loss
end
end V8NativeMessage.N4
