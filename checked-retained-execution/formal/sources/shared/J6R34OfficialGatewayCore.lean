import J6R33OriginalJ6Official
import J6R32RootGeneratedRegistryInputsSite

/-! The thin J6 oracle boundary. A group receipt must refer to the
actual exterior zero child of this same stable chart and exact
prescribed bit word. Resize only the coefficients of the same f
and same receiving precision, then take all 64 group products.
A supplied Meter value alone does not certify any upstream producer. -/
namespace J6R34OfficialGateway
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6R22Active J6R19Retained J6R18ChildWrite J6R9Recursive
open J6Mesh J6OrientedHost J6R11Repack J6R12Repack J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R33OriginalJ6
open J6R32RootGeneratedRegistryInputs J6ActiveRun J6ActiveSchedule J6R12Blueprint
set_option maxHeartbeats 13500000
set_option maxRecDepth 1900
set_option linter.unusedSectionVars false

def frameCopy {f : ℤ[X]} {ell p : ℕ} (hf : f.Monic)
    (oldFrame newFrame : Frame f p) (old : Meter (Block oldFrame ell)) : Meter (Block newFrame ell) :=
  let copy : Meter (Block newFrame ell) := resizeUV ((oldFrame.natDegree hf).trans (newFrame.natDegree hf).symm) old.result
  ⟨copy.result,old.steps+copy.steps+4⟩

theorem frame_copy_exact {f : ℤ[X]} {ell p : ℕ} (hf : f.Monic)
    (oldFrame newFrame : Frame f p) (old : Meter (Block oldFrame ell)) :
    newFrame.decode (frameCopy hf oldFrame newFrame old).result=oldFrame.decode old.result ∧
    (frameCopy hf oldFrame newFrame old).steps≤old.steps+boxFee f.natDegree ell p p+4 := by
  let copy : Meter (Block newFrame ell) :=
    resizeUV ((oldFrame.natDegree hf).trans (newFrame.natDegree hf).symm) old.result
  have hF : 0<f.natDegree := oldFrame.natDegree hf ▸ oldFrame.sizePos
  have n := native_resizeUV oldFrame.hp newFrame.hp hf hF oldFrame.exactMod newFrame.exactMod old.result
  refine ⟨?_,?_⟩
  · change boxTransport newFrame.exactMod (uvRead newFrame.hp newFrame.words ell copy.result)=
      boxTransport oldFrame.exactMod (uvRead oldFrame.hp oldFrame.words ell old.result)
    rw [boxTransport_cast newFrame.exactMod,n.1,boxTransport_cast oldFrame.exactMod]
    exact canonicalLift_spec p f hf ell _
  · change old.steps+copy.steps+4≤_
    exact Nat.add_le_add_right (Nat.add_le_add_left n.2 _) _

section Source
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native ell : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))
variable (hf : f.Monic)
variable (F : Frame f (J6SourcePrecision.printed m base))

structure GroupReceipt (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  frame : Frame f (exteriorChild G ell i j g).prec
  run : Meter (Block frame ell)
  truth : frame.decode run.result =
    reduce (exteriorChild G ell i j g).prec f ell ((exteriorChild G ell i j g).host.contract hf)

theorem exterior_reduction_eq [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (hF : 0<f.natDegree) :
    let child := exteriorChild G ell i j g
    reduce child.prec f ell (child.host.contract hf)=
      zeroChildRun (G.selector ell) (G.ready ell) (G.centre ell i) hf
        (prescribedNode (rootPreset G ell) child.prec ell j) g := by
  let child := exteriorChild G ell i j g
  let z := prescribedNode (rootPreset G ell) child.prec ell j
  have childStable : J6R12Blueprint.Stable (physicalSize m native) 2 child :=
    zeroChild_stable (G.selector ell) (G.ready ell) (G.centre ell i) (G.stable ell) z g
  exact (J6R12Integral.printed_run_exact G.bounds (G.selector ell) child childStable hf hF).symm

noncomputable def groupOnSite (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (R : GroupReceipt (ell:=ell) G hf i j g) : Meter (Block (SiteFrame G ell F i) ell) :=
  frameCopy hf R.frame (SiteFrame G ell F i) R.run

theorem group_on_site_exact [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (R : GroupReceipt (ell:=ell) G hf i j g) :
    let E := SiteFrame G ell F i
    let child := exteriorChild G ell i j g
    E.decode (groupOnSite G hf F i j g R).result=
      zeroChildRun (G.selector ell) (G.ready ell) (G.centre ell i) hf
        (prescribedNode (rootPreset G ell) child.prec ell j) g ∧
    (groupOnSite G hf F i j g R).steps≤R.run.steps+boxFee f.natDegree ell child.prec child.prec+4 := by
  have hF : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
  have copy := frame_copy_exact hf R.frame (SiteFrame G ell F i) R.run
  exact ⟨copy.1.trans (R.truth.trans (exterior_reduction_eq (ell:=ell) G hf i j g hF)),copy.2⟩

noncomputable def completedGroups
    (positive : 0<ell) (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
    (R : ∀ g : Fin 64, GroupReceipt (ell:=ell) G hf i j g) :
    Meter (Block (SiteFrame G ell F i) ell) :=
  let site := SiteFrame G ell F i
  foldM site.hp site.sizePos positive (fun g => groupOnSite G hf F i j g (R g)) (groupOrder 64)

theorem completed_groups_exact [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (positive : 0<ell) (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
    (R : ∀ g : Fin 64, GroupReceipt (ell:=ell) G hf i j g) :
    let E := SiteFrame G ell F i
    let deliver := completedGroups G hf F positive i j R
    E.decode deliver.result =
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) hf (rootPreset G ell) j ∧
    deliver.steps≤bill (fun g=>groupOnSite G hf F i j g (R g)) (groupOrder 64)+
      tupleExtra E.words.length ell (exteriorChild G ell i j (0:Fin 64)).prec 64 := by
  let E := SiteFrame G ell F i
  let value := fun g=>groupOnSite G hf F i j g (R g)
  refine ⟨?_,?_⟩
  · change boxTransport E.exactMod (uvRead E.hp E.words ell
      (foldM E.hp E.sizePos positive value (groupOrder 64)).result)=_
    rw [prodM_value,groupOrder,List.map_ofFn,List.prod_ofFn,map_prod,fallbackTable,zeroRuntime]
    exact Finset.prod_congr rfl (fun g _=>(group_on_site_exact G hf F i j g (R g)).1)
  · have h := (prodM_steps E.hp E.sizePos positive value (groupOrder 64)).2
    simpa only [completedGroups,groupOrder,List.length_ofFn,tupleExtra,Nat.add_assoc] using h

noncomputable def writtenProbe (j : Fin (literalDegree m native+1)) : List Bool :=
  List.ofFn ((rootPreset G ell).word j)

theorem actual_prefix_bytes (j : Fin (literalDegree m native+1)) :
    let B := buildRootBitBank G ell
    writtenProbe (ell:=ell) G j=(B.result.read j).result.val ∧
    writtenProbe (ell:=ell) G j=encodeBits f.natDegree (j.val+1) := by
  let B := buildRootBitBank G ell
  have q := (B.result.consistent j).symm
  exact ⟨q,q.trans ((build_root_probe_receipt G ell).2 j).1⟩

noncomputable def completedOracle [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (positive : 0<ell)
    (R : ∀ i j g, GroupReceipt (ell:=ell) G hf i j g) : CompletedOracle G ell F hf where
  reply := fun i j raw =>
    let E := SiteFrame G ell F i
    if raw=writtenProbe (ell:=ell) G j then (completedGroups G hf F positive i j (R i j)).result
    else (zeroM E.hp).result
  correct := by
    intro i j raw good
    have eq : raw=writtenProbe (ell:=ell) G j := good
    rw [if_pos eq]
    exact (completed_groups_exact G hf F positive i j (R i j)).1

theorem gateway_reply_exact [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (positive : 0<ell) (R : ∀ i j g, GroupReceipt (ell:=ell) G hf i j g)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool)
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    (completedOracle G hf F positive R).reply i j raw =
      (completedGroups G hf F positive i j (R i j)).result ∧
    raw=((buildRootBitBank G ell).result.read j).result.val := by
  have eq : raw=writtenProbe (ell:=ell) G j := legal
  refine ⟨?_,eq.trans (actual_prefix_bytes (ell:=ell) G j).1⟩
  change (if raw=writtenProbe (ell:=ell) G j then (completedGroups G hf F positive i j (R i j)).result
    else (zeroM (f:=(SiteFrame G ell F i).words) (SiteFrame G ell F i).hp).result)=_
  exact if_pos eq
end Source

#print axioms frame_copy_exact
#print axioms exterior_reduction_eq
#print axioms group_on_site_exact
#print axioms completed_groups_exact
#print axioms actual_prefix_bytes
#print axioms gateway_reply_exact
end J6R34OfficialGateway
