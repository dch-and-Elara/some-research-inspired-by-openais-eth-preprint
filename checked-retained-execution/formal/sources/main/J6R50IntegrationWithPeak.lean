import J6R50IntegrationSameRun
import J6R50PeakAbsolute
import J6R50PeakLiteralAtlas

/-! A single source-faithful run has the decoded source answer, restored
directory and the finite scoped occurrence bill. The local raw tariff
hypotheses are deliberately explicit, not consequences of value validity. -/
namespace J6R50Integration
open scoped Polynomial BigOperators
open J6Mesh J6OrientedHost J6R21Ancestor J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R34RootAtlas J6R35RootOrigins J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26StablePreparedRoot J6R24MeteredRecursion J6R48DFS J6R49DFS J6R49Leaf
open J6R30GeneratedRootLayout J6R27OriginalGate J6R24LegalLayout J6R10Repack
open J6R49LiveBits J6R49Cost J6R16ModeCost J6R12Blueprint J6R50Peak

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3200

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
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "pk" => (pageKeyWidth m+pad)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem literal_value_cost_and_selected_peak (basePos : 0<base) (hq : 0<streamQ)
    (ord : ∀ {c : Call (PhysicalHost f ell)},
      Path sel (exteriorChild G ell X.centre X.sample X.group) c → Fin c.edges ≃ c.host.Edge)
    (A : ∀ {c : Call (PhysicalHost f ell)}
      (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
      (h : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges),
      ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable h) T.bank streamQ)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad) → ℕ)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (origin : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (compileFamily I) initial)
    (qFit : streamQ≤uniformWidth s C) (pageBound : ℕ)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel ext x) (w : (Plan sel).Slot x),
      let e := (compileFamily I p w).job.immutable.payload.payload
      ∀ y ∈ e.pages,(originPayload y.payload).length ≤ pageBound)
 :
    let R := literalLeafStreaming X pad I basePos hq ord A
    let run := nativeStream (canonicalStreaming R) retire ext .root initial
    (T.frame (NativeReach.reflexive ext)).decode run.result.1 =
      (sourceBlueprint sel ext X.hf).program.run ext ∧ run.result.2=initial ∧
    run.steps ≤ ∑ j∈Finset.range (pathLimit s C+1),
      levelBill (nativeScopedPlan sel ext) ⟨ext,Path.root⟩
        (actualStreamOwn (canonicalStreaming R) retire initial) j ∧
    ∀ {x : Call (PhysicalHost f ell)} (p : Path sel ext x),
       ∃ mbits nbits, JointSuspensions (canonicalStreaming R) retire initial p mbits nbits ∧
       residentAtlasBits (stackBank R.births initial p)+mbits+nbits ≤
         absoluteSelectedRoof (s:=s) (C:=C) initial (ext).edges (ext).prec pageBound := by
  let R := literalLeafStreaming X pad I basePos hq ord A
  obtain ⟨v,restore,cost⟩ := literal_run_value_and_cost X pad I basePos hq ord A retire initial origin valid
  obtain ⟨_,_,peak⟩ := actual_absolute_source_value_and_selected_peak
    R retire initial origin valid qFit pageBound (actual_compiled_family_census I) bits
  exact ⟨v,restore,cost,peak⟩

#print axioms literal_value_cost_and_selected_peak
end J6R50Integration
