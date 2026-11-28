import V8NativeMessageC3HermiteReadout
import V8NativeMessageC3CanonicalRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4700000

/-! The native MAIN addresses and true private-list register, with
the exact ordinary MAIN origin multiplier. The other D multiplier and
the finite joint margin remain explicit; this is not an arbitrary hybrid. -/
namespace V8NativeMessage.C3.Hermite
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive J6ActiveHermite
open V8PooledMenu.FiveCopy V8PooledRange
noncomputable section

def polyNodeLinear (Q J v : ℕ) : ℚ[X]→ₗ[ℚ]ℚ where
  toFun := nodeReadout Q J v
  map_add' x y := by
    unfold nodeReadout trim
    rw [add_mul,add_modByMonic,eval_add,mul_add]
  map_smul' c x := by
    unfold nodeReadout trim
    rw [smul_mul_assoc,smul_modByMonic,eval_smul]
    simp only [RingHom.id_apply,smul_eq_mul]
    ring

def jetNodeLinear (Q J v : ℕ) : C3.Jet ℚ J→ₗ[ℚ]ℚ :=
  (polyNodeLinear Q J v).comp (AdjoinRoot.modByMonicHom (monic_X.pow J))

namespace Native
open RawMain Canonical
variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]
  {G : Graph V E} {r : ThreePorts G} (F : FiveFile (Γ:=Γ) G r)

def printedJ : ℕ := RawMain.order F.layout

theorem printedJ_positive : 0 < printedJ F := by
  unfold printedJ RawMain.order
  exact Nat.add_pos_left Nat.zero_lt_one _

theorem printedJ_degree_fit :
    directDegree V E * F.layout.R < F.layout.Q*printedJ F := by
  have hQ : 0<F.layout.Q := F.layout.positive_degree.trans F.layout.degree_lt_nodes
  let d := directDegree V E * F.layout.R
  have hrem := Nat.mod_lt d hQ
  have he := Nat.mod_add_div d F.layout.Q
  change d<F.layout.Q*(1+d/F.layout.Q)
  rw [mul_add,mul_one]
  omega

variable (a : RawMain.Address F.layout) {b : Γ→ℕ}
  (Q : NativePrivateLists F a (printedJ F) b)

def nativeOrigin (s : V→Bool) : ℚ :=
  jetNodeLinear F.layout.Q (printedJ F) (positiveNode a.t)
    (actualRegister F a (printedJ F) Q s)

def ordinaryMainLoss : ℕ := coefficientLoss F + extraLoss F.layout.Q (printedJ F)

theorem nativeOrigin_scaled_mem (hw : ∀ g j, Q.weight g j ∈ localJetImage (printedJ F))
    (s : V→Bool) :
    (2:ℚ)^ordinaryMainLoss F*nativeOrigin F a Q s ∈ twoLocalSubalgebra := by
  let J := printedJ F
  have hv : positiveNode a.t∈nodes F.layout.Q :=
    Finset.mem_Icc.mpr (positiveNode_bounds a.t)
  let reg := actualRegister F a J Q s
  let g := AdjoinRoot.modByMonicHom (monic_X.pow J) reg
  change (2:ℚ)^(coefficientLoss F+extraLoss F.layout.Q J)*
    nodeReadout F.layout.Q J (positiveNode a.t) g ∈ twoLocalSubalgebra
  apply node_readout_loss hv (printedJ_positive F)
  intro k _
  exact coefficient_loss F a J Q hw s k

theorem nativeOrigin_multiplier_loss (hw : ∀ g j, Q.weight g j ∈ localJetImage (printedJ F))
    (s : V→Bool) (f : ℤ[X]) (ell : ℕ) :
    HasLoss f ell (ordinaryMainLoss F)
      (algebraMap ℚ (RatRing f ell) (nativeOrigin F a Q s)) := by
  let x : ℚ := nativeOrigin F a Q s
  let u : TwoLocal := ⟨(2:ℚ)^ordinaryMainLoss F*x,nativeOrigin_scaled_mem F a Q hw s⟩
  refine ⟨localScalar f ell u,?_⟩
  rw [embed_localScalar]
  change (2:RatRing f ell)^ordinaryMainLoss F*algebraMap ℚ (RatRing f ell) x =
    algebraMap ℚ (RatRing f ell) ((2:ℚ)^ordinaryMainLoss F*x)
  rw [map_mul,map_pow,map_ofNat]

variable {f : ℤ[X]}

theorem actual_MAIN_origin_canonical_replacement
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (P : Packing G r) (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V)
    (probes : Probes V f) (hf : f.Monic) (s : V→Bool) (q : V8PooledMenu.FiveCopy.Address P hu huM t)
    (sep : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (sep g)=atRoot P hu huM t probes hf s q g)
    (dMult : RatRing f 1) (hd : HasLoss f 1 (ordinaryDLoss t) dMult)
    (fit : ordinaryMainLoss F ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1))) :
    ∃ e : IntRing f 1, (dMult*algebraMap ℚ (RatRing f 1) (nativeOrigin F a Q s))*
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu huM t probes hf s q)) -
        embed f 1 (∏ g, sep g)) =
        embed f 1 ((2:IntRing f 1)^rootPrec V*e) := by
  exact C3_actual_canonical_replacement P hu huM t probes hf s q sep hs
    (algebraMap ℚ (RatRing f 1) (nativeOrigin F a Q s)) dMult
    (nativeOrigin_multiplier_loss F a Q hw s f 1) hd fit

#print axioms polyNodeLinear
#print axioms jetNodeLinear
#print axioms printedJ_positive
#print axioms printedJ_degree_fit
#print axioms nativeOrigin_scaled_mem
#print axioms nativeOrigin_multiplier_loss
#print axioms actual_MAIN_origin_canonical_replacement
end Native
end
end V8NativeMessage.C3.Hermite