import J6R54PublicFamilyQuery
import J6R53PublicMountReadout

/-! The unchanged original per-centre interpolation sees the same raw
blocks at exactly the same legal probe words. Two paid-site Delta
receipts cancel the common oracle boundary, keeping every emitted
public address fee in the genuine interpolation loop. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R34RootAtlas J6R53PublicMount J6R53WordIngress
open J6R14ZeroMode J6R33OriginalJ6 J6R32RootGeneratedRegistryInputs
open J6R36SharedGateway J6R22Active
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 3350
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (R : PublicJobs W C rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
variable (i : J6Recovery.Addr m)

def familySiteFee : ℕ := ∑ j : Fin (literalDegree m native+1),locationFee W i j

def measuredFamilySite : Meter (Block C.frame ell) :=
  paidSite G A (sourcePublicQuery W C R A) C.hf C.positive i

theorem paid_site_is_same_word_and_adds_every_address :
    Delta (measuredFamilySite W C R A i)
      (mountedMeasuredSites G C.hf C.frame C.positive (plainFamily W C R) A i)
      (familySiteFee W i) := by
  let new := sourcePublicQuery W C R A
  let old := paidMountedQuery G C.hf C.frame C.positive (plainFamily W C R) A
  let O := mountedOracle G C.hf C.frame C.positive (plainFamily W C R)
  have Hn := actual_paid_site_delta (F:=C.frame) G A new O
    (fun a b raw h=>actual_public_query_same_original W C R A a b raw h) C.positive i
  have Ho := actual_paid_site_delta (F:=C.frame) G A old O
    (fun a b raw h=>legal_mount_matches_original_oracle G C.hf C.frame C.positive
       (plainFamily W C R) A a b raw h) C.positive i
  refine ⟨Hn.value.trans Ho.value.symm,?_⟩
  let list := probeOrder (literalDegree m native+1)
  let feeNew := list.map (fun j=>(new i j (A.read j).result.val).steps)
  let feeOld := list.map (fun j=>(old i j (A.read j).result.val).steps)
  have stepEq (j : Fin (literalDegree m native+1)) :
      (new i j (A.read j).result.val).steps=
        (old i j (A.read j).result.val).steps+locationFee W i j := by
    unfold new old
    rw [actual_public_query_bill W C R A i j (A.read j).result.val (A.consistent j)]
    exact Nat.add_comm _ _
  have billEq : feeNew.sum=feeOld.sum+familySiteFee W i := by
    simp only [feeNew,feeOld,list,probeOrder,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
      familySiteFee]
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _=>stepEq j)
  change (paidSite G A new C.hf C.positive i).steps=
    (paidSite G A old C.hf C.positive i).steps+familySiteFee W i
  have hn := Hn.fee
  have ho := Ho.fee
  change (paidSite G A new C.hf C.positive i).steps=(oracleSite G A O C.positive i).steps+feeNew.sum at hn
  change (paidSite G A old C.hf C.positive i).steps=(oracleSite G A O C.positive i).steps+feeOld.sum at ho
  rw [hn,ho,billEq]
  omega

#print axioms paid_site_is_same_word_and_adds_every_address
end
end J6R54PublicFamily

