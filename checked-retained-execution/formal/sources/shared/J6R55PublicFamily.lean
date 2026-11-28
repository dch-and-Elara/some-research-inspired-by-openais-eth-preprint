import J6R55PublicMount
import J6R55PublicOrder
import J6R55PublicCapacity
import J6R54PublicFamilyMount

/-! PublicJobs can now share one literal prior registry and one numeric
centre-width guard. They only require the actual stored source drivers
and proof that these drivers consume their real issuers and leaf charts.
No separately supplied edge order or per-group ready/live field occurs. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R51Leaf J6R50Leaf J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R53PublicMount
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 4000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (bp : 0<base)

structure EmittedSiteDriver (W : Widths m native tc tj tw edgew)
    (C : Compiled G ell q rr cc dd prec kp bw) (rate pad : ℕ) (bp : 0<base)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  tree : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf
  source : OnlineMachine tree (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate
  terminal : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
    (x : StoredSite tree v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)),ResidentLeafData x
  chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
    LoopCharts (literalSite W C i j g) pad source bp terminal
  first : UsesFirstIssuer source (issuedAtFirstDepth W C i j g)
  next : UsesChildIncrement source

variable (driver : ∀ i j g, EmittedSiteDriver W C rate pad bp i j g)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
variable (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ)

def publicJobsOfEmittedDrivers
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (slack : 2*m+1+pathLimit (physicalSize m native) 2<2^tc) :
    PublicJobs W C rate pad where
  mount i j g :=
    let D := driver i j g
    mountedRealPublic W C i j g pad D.source B bp (publicExteriorOrder W C i j g)
      D.terminal retire sync old (real_issuance_has_uniform_depth_capacity W C i j g slack)
      D.first D.next D.chart

theorem generated_family_keeps_the_actual_jobs_and_order
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (slack : 2*m+1+pathLimit (physicalSize m native) 2<2^tc)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    let K := (publicJobsOfEmittedDrivers W C bp driver B retire sync old slack).mount i j g
    K.finder=(driver i j g).source ∧ K.initial=B ∧ K.edgeOrder=publicExteriorOrder W C i j g :=
  ⟨rfl,rfl,rfl⟩

#print axioms publicJobsOfEmittedDrivers
#print axioms generated_family_keeps_the_actual_jobs_and_order
end
end J6R55Public

