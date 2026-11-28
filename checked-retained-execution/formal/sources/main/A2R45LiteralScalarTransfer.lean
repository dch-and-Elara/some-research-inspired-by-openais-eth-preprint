
import A2R45LiteralPlacement
import J6R14ZeroModeProbe

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000
set_option maxRecDepth 1930
set_option linter.unusedSectionVars false

/-! Connect the scalar ZMod decoder to the actual App. D receiver.
At the chosen literal address the actual value is precisely the
constant-ring image of the scalar register on the same real seats. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial FixedHostAcquisition A1R43Literal A1R43Literal.General
open J6R10Repack J6R9Recursive J6R12Repack
noncomputable section

variable {n a b : ℕ} (W : General.PairPlan (simulated n) a b)
local notation "P" => General.fullPacking (simulated n) W
local notation "PP" => General.Spare (simulated n) W

def constantIn (p : ℕ) (f : ℤ[X]) : ZMod (2^p)→+*Box f 1 p :=
  (J6ActiveInterpolation.scalarIn p f 1).comp (AdjoinRoot.of (NativeProbeRing.liftPoly p f))

theorem actual_literal_box_is_scalar_mesh (i : Fin (a+1)) (hi : i.val=0)
    (w : Input n) (f : ℤ[X]) (base p : ℕ)
    (hb : 0<base) (hf : f.Monic) (hd : 0<f.natDegree) (hn : 0<n) (hp : n+1<p) :
    (J6R14ZeroMode.polynomial P i (-1) p (file (Pad:=PP) w f base) hf).eval 0 =
      constantIn p f ((fixedMeshSlot (K:=ZMod (2^p)) (2^(a+1)) (realPlacement W) w.enabled)) := by
  rw [native_zero_polynomial P i hi w f base p hb (by omega) hf hd hn
    (General.full_seat_predecessor (simulated n) W)]
  let h := fixedMeshSlot (K:=ZMod (2^p)) (2^(a+1)) (realPlacement W) w.enabled
  have hi' : h.val=count w.enabled := actual_scalar_mesh_decode W w p hn hp
  have e : (h.val:ZMod (2^p))=h := by
    letI : NeZero (2^p:ℕ) := ⟨pow_ne_zero _ (by decide)⟩
    exact ZMod.natCast_zmod_val h
  rw [hi'] at e
  change (count w.enabled:Box f 1 p)=constantIn p f h
  rw [←e,map_natCast]

theorem actual_literal_box_readout (i : Fin (a+1)) (hi : i.val=0)
    (w : Input n) (f : ℤ[X]) (base p : ℕ)
    (hb : 0<base) (hf : f.Monic) (hd : 0<f.natDegree) (hn : 0<n) (hp : n+1<p) :
    boxNatural f 1 p hf
      ((J6R14ZeroMode.polynomial P i (-1) p (file (Pad:=PP) w f base) hf).eval 0) =
      (fixedMeshSlot (K:=ZMod (2^p)) (2^(a+1)) (realPlacement W) w.enabled).val := by
  rw [native_zero_polynomial P i hi w f base p hb (by omega) hf hd hn
    (General.full_seat_predecessor (simulated n) W),actual_scalar_mesh_decode W w p hn hp]
  exact boxNatural_of_nat f 1 p hf (by omega) (by decide) hd _
    ((count_le w.enabled).trans_lt (Nat.pow_lt_pow_right (by decide) hp))

#print axioms actual_literal_box_is_scalar_mesh
#print axioms actual_literal_box_readout
end
end A2R45Literal
