import J6R54PublicFamilySite
import J6R53WordIngressCharge
import J6R53PublicMountGateway

/-! At each public query the one freshly emitted head is captured by the
64-group loop. Compiled graph, frame, common word material and code
tape are shared. Native resident executors are specific to this exact
generated site; they do not supply any duplicated setup fields. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R14ZeroMode J6R33OriginalJ6
open J6R34RootAtlas J6R53PublicMount J6R53WordIngress
open J6R32RootGeneratedRegistryInputs
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 3300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew)
variable (C : Compiled G ell q rr cc dd prec kp bw)
variable {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)}
variable (g : Fin 64) (H : ExactHead m native tc tj tw i j)

abbrev MountedAt :=
  MountedGroup (rate:=rate) (pad:=pad) G (siteFromHead W g C H).result

def issueMountedAt (R : MountedAt (rate:=rate) (pad:=pad) W C g H) :
    Meter (AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
      (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=KeyWidth kp tc tj) (prec:=prec)
      (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad) G i j g) :=
  let X := siteFromHead W g C H
  let h := site_keeps_shared_payload W g C H
  ⟨⟨X.result,R,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩,X.steps+3⟩

theorem issued_mounted_at_exact (R : MountedAt (rate:=rate) (pad:=pad) W C g H) :
    (issueMountedAt W C g H R).result.source=(siteFromHead W g C H).result ∧
      (issueMountedAt W C g H R).steps=ordinalFee 6 g.val+11 := by
  refine ⟨rfl,?_⟩
  change (siteFromHead W g C H).steps+3=_
  rw [site_exact_local_fee W g C H]

structure PublicJobs (W : Widths m native tc tj tw edgew)
    (C : Compiled G ell q rr cc dd prec kp bw) (rate pad : ℕ) where
  mount : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
    MountedGroup (rate:=rate) (pad:=pad) G (siteFromHead W g C (prepareHead W i j).result).result

variable (R : PublicJobs W C rate pad)

def plainFamily : MountedFamily G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw rate pad :=
  fun i j g => (issueMountedAt W C g (prepareHead W i j).result (R.mount i j g)).result

def cachedPublicSlot (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    Meter (Block (SiteFrame G ell C.frame i) ell) :=
  let H := prepareHead W i j
  let P := fun g => issueMountedAt W C g H.result (R.mount i j g)
  let M := mountedSlotPaidIngress G C.hf C.frame i j C.positive P
  ⟨M.result,H.steps+M.steps+4⟩

theorem cached_slot_exact_plain_and_fee (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
    let M := mountedSlot G C.hf C.frame i j C.positive (plainFamily W C R i j)
    (cachedPublicSlot W C R i j).result=M.result ∧
      (cachedPublicSlot W C R i j).steps=(prepareHead W i j).steps+
        (M.steps+∑ g : Fin 64,(ordinalFee 6 g.val+11))+4 := by
  let P := fun g => issueMountedAt W C g (prepareHead W i j).result (R.mount i j g)
  have H := original_slot_adds_each_ingress_once G C.hf C.frame i j C.positive P
  refine ⟨H.1,?_⟩
  change (prepareHead W i j).steps+(mountedSlotPaidIngress G C.hf C.frame i j C.positive P).steps+4=_
  rw [H.2]
  have F : (∑ g : Fin 64,(P g).steps)=∑ g : Fin 64,(ordinalFee 6 g.val+11) :=
    Finset.sum_congr rfl (fun g _=>(issued_mounted_at_exact W C g (prepareHead W i j).result (R.mount i j g)).2)

  rw [F]
  rfl

#print axioms issueMountedAt
#print axioms issued_mounted_at_exact
#print axioms cachedPublicSlot
#print axioms cached_slot_exact_plain_and_fee
end
end J6R54PublicFamily

