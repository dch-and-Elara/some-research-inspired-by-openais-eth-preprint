import J6R53PublicMountAggregate

/-! Metered ingress is consumed once at the original 64 children.
Only the receipt fee changes: the exact original frame-copy and
product run on the same raw blocks, not simulated decode values. -/
namespace J6R53WordIngress
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R34RootAtlas J6R53PublicMount J6R22Active
open J6R14ZeroMode J6R33OriginalJ6 J6R32RootGeneratedRegistryInputs
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3250
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false
set_option Elab.async false

def addIngressCharge {A : Type*} (M : Meter A) (charge : ℕ) : Meter A :=
  ⟨M.result,charge+M.steps⟩

theorem paid_fold_exact {A : Type*} {p ell : ℕ} {f : List (A1R10.Word p)}
    (hp : 0<p) (he : 0<f.length) (hv : 0<ell)
    (read : A→Meter (UVBlock f ell)) (charge : A→ℕ) (xs : List A) :
    let charged := fun x=>addIngressCharge (read x) (charge x)
    (foldM hp he hv charged xs).result=(foldM hp he hv read xs).result ∧
      (foldM hp he hv charged xs).steps=(foldM hp he hv read xs).steps+(xs.map charge).sum := by
  dsimp only
  have H := product_delta hp he hv (fun x=>addIngressCharge (read x) (charge x)) read charge xs
    (fun x _=>⟨rfl,by simp [addIngressCharge,Nat.add_comm]⟩)
  exact ⟨H.value,H.fee⟩

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]



variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base))
variable (i : J6Recovery.Addr m) (j : Fin (J6R14ZeroMode.literalDegree m native+1))
variable {g : Fin 64}

def addGroupCharge (R : GroupReceipt (ell:=ell) G hf i j g) (charged : ℕ) :
    GroupReceipt (ell:=ell) G hf i j g where
  frame := R.frame
  run := addIngressCharge R.run charged
  truth := R.truth

theorem charge_frame_copy_exact (R : GroupReceipt (ell:=ell) G hf i j g) (charged : ℕ) :
    groupOnSite G hf F i j g (addGroupCharge G hf i j R charged) =
       addIngressCharge (groupOnSite G hf F i j g R) charged := by
  let E := SiteFrame G ell F i
  let C : Meter (Block E ell) := J6R19Retained.resizeUV
    ((R.frame.natDegree hf).trans (E.natDegree hf).symm) R.run.result
  change (⟨C.result,(charged+R.run.steps)+C.steps+4⟩ : Meter (Block E ell)) =
    ⟨C.result,charged+(R.run.steps+C.steps+4)⟩
  have same : (charged+R.run.steps)+C.steps+4=charged+(R.run.steps+C.steps+4) := by omega
  rw [same]

variable (positive : 0<ell)
variable (P : ∀ g : Fin 64, Meter (AddressGroup
  (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew) (tc:=tc) (tj:=tj)
  (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad) G i j g))

def chargedReceipt (g : Fin 64) : GroupReceipt (ell:=ell) G hf i j g :=
  let M := P g
  addGroupCharge G hf i j (addressedReceipt G hf F i j M.result) M.steps

def mountedSlotPaidIngress : Meter (Block (SiteFrame G ell F i) ell) :=
  completedGroups G hf F positive i j (chargedReceipt G hf F i j P)

theorem original_slot_adds_each_ingress_once :
    (mountedSlotPaidIngress G hf F i j positive P).result=
       (mountedSlot G hf F i j positive (fun g=>(P g).result)).result ∧
      (mountedSlotPaidIngress G hf F i j positive P).steps=
       (mountedSlot G hf F i j positive (fun g=>(P g).result)).steps+
        ∑ g : Fin 64,(P g).steps := by
  let E := SiteFrame G ell F i
  let read := fun g : Fin 64 => groupOnSite G hf F i j g (addressedReceipt G hf F i j (P g).result)
  let charge := fun g : Fin 64 => (P g).steps
  let run := fun g : Fin 64 => groupOnSite G hf F i j g (chargedReceipt G hf F i j P g)
  have same : run=(fun g=>addIngressCharge (read g) (charge g)) := by
    funext g
    exact charge_frame_copy_exact G hf F i j _ _
  have H := paid_fold_exact E.hp E.sizePos positive read charge (groupOrder 64)
  change (foldM E.hp E.sizePos positive run (groupOrder 64)).result=
      (foldM E.hp E.sizePos positive read (groupOrder 64)).result ∧
    (foldM E.hp E.sizePos positive run (groupOrder 64)).steps=
      (foldM E.hp E.sizePos positive read (groupOrder 64)).steps+_
  rw [same]
  refine ⟨H.1,?_⟩
  rw [H.2,groupOrder,List.map_ofFn,List.sum_ofFn]
  rfl

#print axioms paid_fold_exact
#print axioms charge_frame_copy_exact
#print axioms original_slot_adds_each_ingress_once
end
end J6R53WordIngress

