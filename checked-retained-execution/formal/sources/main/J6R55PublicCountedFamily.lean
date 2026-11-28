import J6R55PublicBootToDriver
import J6R55PublicCountBridge

/-! A family indexed by the actual emitted public addresses.  Each
member uses the one shared compiled frame and initial bank.  The actual
per-site native words and the original terminal chart are retained. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R22RootReadout
open J6R51Ingress J6R52FreshShape J7R9Compiler J7R9Subdivision J7R10Plant
open J6R53PublicMount J6R49RootIngress J6R50RootIngress J6R54PublicFamily
open J6R32RootGeneratedRegistryInputs J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R14ZeroMode J6R31RootResidentTables J6R16ModeCost
open J6R51 J6R51Online J6R51Leaf J6R50Leaf J6R48DFS
open J6R15ModeCost J6R32StatefulArithmetic J6R30ProducedGateRegistry J6R50SourceProducer
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R35RootOrigins J6R54ExteriorOwner
open J6R55TerminalBootJoined J6R55BootBodies J6R54TerminalBoot
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 23000000
set_option maxRecDepth 5200
set_option Elab.async false

noncomputable section
section Recipe
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

structure PublicNativeRecipe
    (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
    (rate pad : ℕ)
    (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
      (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)
    (sync : B.synced) (old : ∀ a∈B.headers,a.id.val≤C.mark.val) (bp : 0<base)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  tree : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf
  operators : OnlineOperators tree (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate
  gate : Stamp (KeyWidth kp tc tj) prec
  own : ℕ
  name : SourceVertex A→J6R15ModeCost.Word own
  root : RootRoster (P:=A) gate pad name
  writer : FirstBodyProgram (literalSite W C i j g) gate pad tree
  owners : OwnerWordsAtBodies (literalSite W C i j g) gate pad root writer
  rootInj : Function.Injective name
  requests : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
    (Y : StoredSite tree v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (u : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest Y u)
  terminal : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
    (Y : StoredSite tree v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)), ResidentLeafData Y
  chart : letI := sourceDecision (G.selector ell) (exteriorChild G ell i j g)
    LoopCharts (literalSite W C i j g) pad
      (stampedPublicMachine W C i j g pad operators B gate root writer owners rootInj requests sync old)
      bp terminal

variable {W : Widths m native tc tj tw edgew} {C : Compiled G ell q rr cc dd prec kp bw}
variable {rate pad : ℕ}
variable {B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad}
variable {sync : B.synced} {old : ∀ a∈B.headers,a.id.val≤C.mark.val} {bp : 0<base}
variable {i : J6Recovery.Addr m} {j : Fin (literalDegree m native+1)} {g : Fin 64}
variable (R : PublicNativeRecipe W C rate pad B sync old bp i j g)

def driverFromPublicRecipe : EmittedSiteDriver W C rate pad bp i j g :=
  stampedPublicDriver W C i j g pad R.operators B R.gate R.root R.writer R.owners R.rootInj
    R.requests bp R.terminal sync old R.chart

theorem recipe_keeps_actual_source :
    (driverFromPublicRecipe R).source=
      stampedPublicMachine W C i j g pad R.operators B R.gate R.root R.writer R.owners R.rootInj
        R.requests sync old := rfl
end Recipe

section Submitted
attribute [local irreducible] J6R51Ingress.freshPlant J6R51Ingress.guardedInOrder
attribute [local irreducible] runMountedCount runPreparedCount

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
variable {f : ℤ[X]} {base native ell q rr cc dd edgew tc tj prec tw bw rate pad kp : ℕ}
variable (G : RootShape f (nWires (guardedInOrder F order.roster))
  (printedHalf (nWires (guardedInOrder F order.roster))) base native
  (printedRankWidth (nWires (guardedInOrder F order.roster)))
  (freshPlant (guardedInOrder F order.roster) (guardRoster order))
  (constantRootWord (nWires (guardedInOrder F order.roster))))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (W : Widths (nWires (guardedInOrder F order.roster)) native tc tj tw edgew)
variable (bp : 0<base)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=nWires (guardedInOrder F order.roster)) pad)
variable (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw
  (pageKeyWidth (nWires (guardedInOrder F order.roster))+pad)→ℕ)
variable (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤(prepareShared I).result.mark.val)
variable (slack : 2*nWires (guardedInOrder F order.roster)+1+
  pathLimit (physicalSize (nWires (guardedInOrder F order.roster)) native) 2<2^tc)
variable (recipes : ∀ i j g, PublicNativeRecipe W (prepareShared I).result rate pad B sync old bp i j g)

/-- Dispatcher assembly for every original legal public address.  No
PublicJobs value is supplied. -/
def countedRecipeJobs : PublicJobs W (prepareShared I).result rate pad :=
  publicJobsOfEmittedDrivers W (prepareShared I).result bp
    (fun i j g=>driverFromPublicRecipe (recipes i j g)) B retire sync old slack

def countedPublicRecipeFamily :=
  runPreparedCount W I (countedRecipeJobs F order G I W bp B retire sync old slack recipes)

theorem actual_counted_recipe_family_word_and_bill :
    let S := prepareShared I
    let jobs := countedRecipeJobs F order G I W bp B retire sync old slack recipes
    let out := countedPublicRecipeFamily F order G I W bp B retire sync old slack recipes
    let orig := runMountedCount G S.result.hf S.result.frame S.result.positive (plainFamily W S.result jobs)
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps=orig.steps+S.steps+allLocationFee W :=
  actual_emitted_driver_CNF_count_and_bill F order G I W bp
    (fun i j g=>driverFromPublicRecipe (recipes i j g)) B retire sync old slack
end Submitted

#print axioms driverFromPublicRecipe
#print axioms recipe_keeps_actual_source
#print axioms countedRecipeJobs
#print axioms countedPublicRecipeFamily
#print axioms actual_counted_recipe_family_word_and_bill
end
end J6R55Public

