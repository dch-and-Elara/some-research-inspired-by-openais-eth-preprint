import J6R50IntegrationSameRun

/-! The cost conclusion for the same literal-leaf run follows from
three phase budgets on that very run. No uncharged masks, input
routes, site selection, or physical deallocation are inferred. -/
namespace J6R50Integration
open scoped Polynomial
open J6Mesh J6OrientedHost J6R21Ancestor J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R34RootAtlas J6R35RootOrigins J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26StablePreparedRoot J6R24MeteredRecursion J6R48DFS J6R49DFS J6R49Leaf
open J6R30GeneratedRootLayout J6R27OriginalGate J6R24LegalLayout J6R10Repack
open J6R49LiveBits J6R49Cost J6R16ModeCost

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3200

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem whole_stream_under_three_phase_caps
    (R : StreamingResident T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page → ℕ)
    (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack R.births initial) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (fixed arithmetic publication : ℕ)
    (leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff),
      (R.leaf z.2 stop (stackBank R.births initial z.2)).steps≤fixed)
    (active : ∀ (z : Sigma (Path sel r)) (ha : (printedParams (f:=f) (ell:=ell) s).cutoff<z.1.edges),
      streamActiveTariff (R.active z.2 ha) (reachable_positive T z.2.reached) T.vPositive≤
        fixed+arithmetic*Nat.card ((Plan sel).Slot z.1))
    (publish : ∀ (z : Sigma (Path sel r)) (w : (Plan sel).Slot z.1),
      scopedPublishCharge R.births initial z.2 w retire≤publication) :
    (nativeStream R retire r .root initial).steps≤
      (pathLimit s C+1)*(fixed+(arithmetic+publication))*
        2^(branchBits (Nat.clog 2 s)*(pathLimit s C+1)+
          24*depthScale s C (Nat.clog 2 s) (siteConstant C)) :=
  actual_stream_under_local_bit_tariffs R retire initial legal hzero hroot fixed
    (arithmetic+publication)
    (actual_local_tariff_from_phase_caps R retire initial fixed arithmetic publication leaf active publish)

#print axioms whole_stream_under_three_phase_caps
end J6R50Integration

