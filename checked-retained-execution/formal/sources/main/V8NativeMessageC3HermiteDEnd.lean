import V8NativeMessageC3HermiteDWeight
import V8NativeMessageC3HermitePrintedGuards
import V8NativeMessageC3MainCoefficientBridge
import V8NativeMessageC3CanonicalAssembly

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! Both ordinary source multipliers, at an actual MAIN private register
and actual D probe/mode address, using exactly the finite reserve printed
at that D creation site. -/
namespace V8NativeMessage.C3.Hermite.Native
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral
open V8PooledMenu.FiveCopy V8PooledRange
open RawMain Canonical
noncomputable section

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]
  {G : Graph V E} {r : ThreePorts G} {f : ℤ[X]}
  (F : FiveFile (Γ:=Γ) G r) (a : RawMain.Address F.layout) {b : Γ→ℕ}
  (Q : NativePrivateLists F a (printedJ F) b)
  (P : Packing G r) (hu : 0<rootU V) (hM : rootU V≤wireSize V)
  (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V→Bool)

def ordinaryCrossWeight (q : V8PooledMenu.FiveCopy.Address P hu hM t) : RatRing f 1 :=
  D.dPublicWeight V t probes hf q.probeIdx *
    algebraMap ℚ (RatRing f 1) (nativeOrigin F a Q s)

theorem ordinary_cross_weight_loss
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (q : V8PooledMenu.FiveCopy.Address P hu hM t) :
    HasLoss f 1 (ordinaryDLoss t+ordinaryMainLoss F)
      (ordinaryCrossWeight F a Q P hu hM t probes hf s q) :=
  loss_mul (D.actual_D_probe_multiplier_loss V t hu hM probes hf q.probeIdx)
    (nativeOrigin_multiplier_loss F a Q hw s f 1)

theorem ordinary_cross_slot_replacement
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (q : V8PooledMenu.FiveCopy.Address P hu hM t)
    (sep : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (sep g)=atRoot P hu hM t probes hf s q g)
    (fit : ordinaryMainLoss F ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1))) :
    ∃ e : IntRing f 1, ordinaryCrossWeight F a Q P hu hM t probes hf s q *
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu hM t probes hf s q)) -
        embed f 1 (∏ g, sep g)) = embed f 1 ((2:IntRing f 1)^rootPrec V*e) :=
  actual_MAIN_origin_canonical_replacement F a Q hw P hu hM t probes hf s q sep hs
    (D.dPublicWeight V t probes hf q.probeIdx)
    (D.actual_D_probe_multiplier_loss V t hu hM probes hf q.probeIdx) fit

/-- The sum can contain any fixed enumeration of native probe/mode slots,
including repeats. Integrality is required only of the assembled sum. -/
theorem ordinary_cross_sum_replacement {I : Type} [Fintype I]
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (address : I→V8PooledMenu.FiveCopy.Address P hu hM t)
    (sep : I→Fin 64→IntRing f 1)
    (hs : ∀ i g, reduce (high t) f 1 (sep i g)=
      atRoot P hu hM t probes hf s (address i) g)
    (fit : ordinaryMainLoss F ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1)))
    (A : IntRing f 1)
    (hA : (∑ i, ordinaryCrossWeight F a Q P hu hM t probes hf s (address i) *
      embed f 1 (canonicalLift (high t) f hf 1
        (wholeHigh P hu hM t probes hf s (address i)))) = embed f 1 A) :
    ∃ B : IntRing f 1, (∑ i, ordinaryCrossWeight F a Q P hu hM t probes hf s (address i) *
      embed f 1 (∏ g, sep i g)) = embed f 1 B ∧
      reduce (rootPrec V) f 1 B=reduce (rootPrec V) f 1 A := by
  apply assemble_replacements hf _ _ A hA
  intro i
  simp only [←mul_sub]
  exact ordinary_cross_slot_replacement F a Q P hu hM t probes hf s hw
    (address i) (sep i) (hs i) fit

/-- The published MAIN and D schedules, with a concrete uniform onset.
No supplied shift-integrality test or abstract precision-fit premise. -/
theorem ordinary_cross_slot_replacement_printed
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (hprinted : F.layout.Q=sourceQ V) (hlarge : 15≤rootU V)
    (q : V8PooledMenu.FiveCopy.Address P hu hM t)
    (sep : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (sep g)=atRoot P hu hM t probes hf s q g) :
    ∃ e : IntRing f 1, ordinaryCrossWeight F a Q P hu hM t probes hf s q *
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu hM t probes hf s q)) -
        embed f 1 (∏ g, sep g)) = embed f 1 ((2:IntRing f 1)^rootPrec V*e) :=
  ordinary_cross_slot_replacement F a Q P hu hM t probes hf s hw q sep hs
    (ordinary_main_printed_margin F hprinted hlarge hM t)

theorem ordinary_coefficient_cross_slot_replacement_printed
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (hprinted : F.layout.Q=sourceQ V) (hlarge : 15≤rootU V) (j : ℕ)
    (q : V8PooledMenu.FiveCopy.Address P hu hM t)
    (sep : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (sep g)=atRoot P hu hM t probes hf s q g) :
    ∃ e : IntRing f 1, (D.dPublicWeight V t probes hf q.probeIdx *
      algebraMap ℚ (RatRing f 1) (jetCoeff (printedJ F) j (actualRegister F a (printedJ F) Q s))) *
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu hM t probes hf s q)) -
        embed f 1 (∏ g, sep g)) = embed f 1 ((2:IntRing f 1)^rootPrec V*e) :=
  C3_actual_coefficient_replacement F a (printedJ F) Q hw j P hu hM t probes hf s q sep hs
    (D.dPublicWeight V t probes hf q.probeIdx)
    (D.actual_D_probe_multiplier_loss V t hu hM probes hf q.probeIdx)
    ((Nat.le_add_right _ _ : coefficientLoss F≤ordinaryMainLoss F).trans
      (ordinary_main_printed_margin F hprinted hlarge hM t))

/-- Full published numerical MAIN guard. The size threshold is deduced,
not supplied independently. The address remains the original one. -/
theorem ordinary_cross_slot_full_printed_guards
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (hQ : F.layout.Q=sourceQ V) {β : ℕ} (hβ : 1≤β)
    (hR : F.layout.R=sourceR V β) (h6 : 6*F.layout.R≤F.layout.Q)
    (q : V8PooledMenu.FiveCopy.Address P hu hM t)
    (sep : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (sep g)=atRoot P hu hM t probes hf s q g) :
    ∃ e : IntRing f 1, ordinaryCrossWeight F a Q P hu hM t probes hf s q *
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu hM t probes hf s q)) -
        embed f 1 (∏ g, sep g)) = embed f 1 ((2:IntRing f 1)^rootPrec V*e) :=
  ordinary_cross_slot_replacement_printed F a Q P hu hM t probes hf s hw hQ
    (source_guards_force_large F hQ hβ hR h6) q sep hs

#print axioms ordinary_cross_slot_full_printed_guards
#print axioms ordinary_cross_slot_replacement_printed
#print axioms ordinary_coefficient_cross_slot_replacement_printed
#print axioms ordinary_cross_weight_loss
#print axioms ordinary_cross_slot_replacement
#print axioms ordinary_cross_sum_replacement
end
end V8NativeMessage.C3.Hermite.Native
