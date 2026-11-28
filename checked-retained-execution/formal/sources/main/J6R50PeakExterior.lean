
import J6R50PeakAbsolute
import J6R50PeakLiteralAtlas
import J6R49LiveLiteralRun

/-! The actual exterior run has absolute depth one. Its prepared
compiled family supplies the atlas census automatically. The word
width and individual OriginFields payload bounds remain explicit. -/
namespace J6R50Peak
open scoped Polynomial
open J6Mesh J6OrientedHost J6R21Ancestor J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R34RootAtlas J6R35RootOrigins J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26StablePreparedRoot J6R24MeteredRecursion J6R48DFS J6R49DFS J6R49Leaf
open J6R30ProducedGateRegistry J6R30GeneratedRootLayout J6R27OriginalGate J6R24LegalLayout
open J6R10Repack J6R49LiveBits J6R16ModeCost

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 21000000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C streamQ : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
variable (I : InputFamily T key prec tw bw (pageKeyWidth m+pad))
variable [DecidableEq (Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem original_exterior_selected_peak
    (basePos : 0<base) (hq : 0<streamQ) (qFit : streamQ≤uniformWidth s C)
    (ord : ∀ {c : Call (PhysicalHost f ell)},
      Path sel (exteriorChild G ell X.centre X.sample X.group) c → Fin c.edges ≃ c.host.Edge)
    (A : ∀ {c : Call (PhysicalHost f ell)}
      (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges),
      ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable a) T.bank streamQ)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad) → ℕ)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (origin : IsLive (X.seed pad) initial)
    (legal : ReadyOnStack (compileFamily I) initial)
    (pageBound : ℕ)
    (bits : ∀ {c : Call (PhysicalHost f ell)}
      (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c),
      let e := (compileFamily I p w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound) :
    let ext := exteriorChild G ell X.centre X.sample X.group
    let R := literalLeafStreaming X pad I basePos hq ord A
    let run := nativeStream (canonicalStreaming R) retire ext .root initial
    ext.depth=1 ∧
    (T.frame (NativeReach.reflexive ext)).decode run.result.1=(sourceBlueprint sel ext X.hf).program.run ext ∧
    run.result.2=initial ∧
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c),
      ∃ u v,JointSuspensions (canonicalStreaming R) retire initial p u v ∧
        residentAtlasBits (stackBank (compileFamily I) initial p)+u+v≤
          absoluteSelectedRoof (s:=s) (C:=C) initial ext.edges ext.prec pageBound := by
  exact ⟨rfl,actual_absolute_source_value_and_selected_peak
    (literalLeafStreaming X pad I basePos hq ord A) retire initial origin legal qFit pageBound
      (actual_compiled_family_census I) bits⟩

#print axioms original_exterior_selected_peak
end J6R50Peak
