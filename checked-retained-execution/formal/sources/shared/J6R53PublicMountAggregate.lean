import J6R53PublicMountCore

/-! Reindex the installed job by the literal public source address,
preserving its bill before the original all-64 completion product. -/
namespace J6R53PublicMount
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R34RootAtlas J6R27OriginalGate J6R14ZeroMode
open J6R32RootGeneratedRegistryInputs J6R19Retained

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3310
set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))
local notation "Site" => (StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
local notation "Receipt" => (GroupReceipt (ell:=ell) G)

structure AddressGroup (i : Centre) (j : Sample) (g : Fin 64) where
  source : Site
  job : MountedGroup (rate:=rate) (pad:=pad) G source
  sameCentre : source.centre=i
  sameSample : source.sample.val=j.val
  sameGroup : source.group=g

private def atAddress
    {i i' : Centre} {j j' : Sample} {g g' : Fin 64} {old_H new_H : f.Monic}
    (hi : i=i') (hj : j=j') (hg : g=g') (r : Receipt old_H i j g) :
    Receipt new_H i' j' g' := by
  cases hi
  cases hj
  cases hg
  exact r

private theorem atAddress_steps
    {i i' : Centre} {j j' : Sample} {g g' : Fin 64} {old_H new_H : f.Monic}
    (hi : i=i') (hj : j=j') (hg : g=g') (r : Receipt old_H i j g) :
    (atAddress G (new_H:=new_H) hi hj hg r).run.steps=r.run.steps := by
  cases hi
  cases hj
  cases hg
  rfl

variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base))
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
variable {g : Fin 64}
variable (A : AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew)
  (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad) G i j g)

def addressedReceipt : Receipt hf i j g :=
  atAddress G A.sameCentre (Fin.ext A.sameSample) A.sameGroup
    (mountedReceipt G A.source A.job (F.natDegree hf ▸ F.sizePos))

def groupCharge : ℕ :=
  installSteps G A.source A.job + (afterInstall G A.source A.job).steps +4

theorem addressed_receipt_exact_bill : (addressedReceipt G hf F i j A).run.steps=groupCharge G i j A :=
  (atAddress_steps G (new_H:=hf) A.sameCentre (Fin.ext A.sameSample) A.sameGroup
    (mountedReceipt G A.source A.job (F.natDegree hf ▸ F.sizePos))).trans
      (receipt_includes_install_and_dfs G A.source A.job (F.natDegree hf ▸ F.sizePos))

variable (positive : 0<ell)
variable (R : ∀ g : Fin 64, AddressGroup (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew)
  (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad) G i j g)

def mountedSlot : Meter (Block (SiteFrame G ell F i) ell) :=
  completedGroups G hf F positive i j (fun g => addressedReceipt G hf F i j (R g))

theorem mounted_public_slot_is_original :
    (SiteFrame G ell F i).decode (mountedSlot G hf F i j positive R).result =
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) hf (rootPreset G ell) j :=
   (completed_groups_exact G hf F positive i j (fun g=> addressedReceipt G hf F i j (R g))).1

theorem all_sixty_four_installs_and_runs_are_paid :
    (∑ g : Fin 64, groupCharge G i j (R g)) ≤ (mountedSlot G hf F i j positive R).steps := by
  let E := SiteFrame G ell F i
  let read := fun h : Fin 64=>groupOnSite G hf F i j h (addressedReceipt G hf F i j (R h))
  have count : bill read (groupOrder 64)≤(mountedSlot G hf F i j positive R).steps :=
    (prodM_steps E.hp E.sizePos positive read (groupOrder 64)).1
  refine le_trans ?_ count
  unfold bill groupOrder
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  apply Finset.sum_le_sum
  intro h _
  rw [←addressed_receipt_exact_bill G hf F i j (R h)]
  change (addressedReceipt G hf F i j (R h)).run.steps≤
      (addressedReceipt G hf F i j (R h)).run.steps+_+4
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem all_sixty_four_installs_envelope :
    let p := (exteriorChild G ell i j (0:Fin 64)).prec
    let E := SiteFrame G ell F i
    (mountedSlot G hf F i j positive R).steps ≤
      (∑ g : Fin 64,groupCharge G i j (R g))+
        64*(boxFee f.natDegree ell p p+4)+tupleExtra E.words.length ell p 64 := by
  let p := (exteriorChild G ell i j (0:Fin 64)).prec
  let E := SiteFrame G ell F i
  let read := fun h : Fin 64=>groupOnSite G hf F i j h (addressedReceipt G hf F i j (R h))
  have agg := (completed_groups_exact G hf F positive i j (fun h=>addressedReceipt G hf F i j (R h))).2
  change (mountedSlot G hf F i j positive R).steps≤bill read (groupOrder 64)+
    tupleExtra E.words.length ell p 64 at agg
  refine agg.trans (Nat.add_le_add_right ?_ _)
  unfold bill groupOrder
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  calc
    (∑ h : Fin 64,(read h).steps)≤
        ∑ h : Fin 64,(groupCharge G i j (R h)+(boxFee f.natDegree ell p p+4)) := by
      apply Finset.sum_le_sum
      intro h _
      have d := (group_on_site_exact G hf F i j h (addressedReceipt G hf F i j (R h))).2
      change (read h).steps≤(addressedReceipt G hf F i j (R h)).run.steps+
        boxFee f.natDegree ell p p+4 at d
      rw [addressed_receipt_exact_bill G hf F i j (R h)] at d
      simpa only [Nat.add_assoc] using d
    _ = _ := by simp [Finset.sum_add_distrib,p]

#print axioms addressed_receipt_exact_bill
#print axioms mounted_public_slot_is_original
#print axioms all_sixty_four_installs_and_runs_are_paid
#print axioms all_sixty_four_installs_envelope
end
end J6R53PublicMount
