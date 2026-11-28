import J6R65LeafRateNumerics
import J6R62LeafSized
import J6R57PublicNoChartOnline
import J6R51OnlineFeeDefs
import J6R64BootSeatsNative
import J6R58LeafScaleBook

/-! The root and zero-edge cases of the very same paid owner runtime.
They run the preserved literal evaluator, not the positive owner compiler.
The zero branch still visits every isolated row but only one assignment. -/
namespace J6R65LeafRate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6Mesh J6OrientedHost J6R34RootAtlas J6R35RootOrigins
open J6R26DescriptorTree J6R34ChildPath J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf J6R48DFS
open J6R57Public J6R57LeafCap J6R58LeafScale J6R62Leaf J6R25PreparedSupply
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R37StructuredRoot J6R41StructuredAllPaths J6R48RawRoute J6R22Active

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 34000000
set_option maxRecDepth 4500

noncomputable section
def sourceArithmetic {f : ℤ[X]} {ell : ℕ} (s C : ℕ) (r : Call (PhysicalHost f ell)) : ℕ :=
  leafArithmeticScale (4*Nat.clog 2 s) ell (r.prec+160*C*s^2)
    (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) (vertexCount r.host+4*(C*s)) 0

private theorem canonical_tape_rows {f : ℤ[X]} {ell key page : ℕ}
    {c : Call (PhysicalHost f ell)}
    (h : c.host.edgeCount=c.edges) (cmd : Vertex c→PageReadCode c.edges key page) :
    (PagedLeaf.toRaw (orderedCommands h cmd)).rows.length=vertexCount c.host :=
  true_ordered_leaf_keeps_all_vertices h cmd

section ZeroBook
variable {f : ℤ[X]} {ell s C key prec tw bw pg : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (par : Path sel r c) (w : (Plan sel).Slot c)
variable (Y : StoredSite T (par.ticket w) key prec tw bw pg)

def observedBookBodyWidth : ℕ :=
  observedMax (fun a=>a.body.length) Y.birth.native.physical.raw

def zeroBookSetup : ℕ :=
  10+2*(C*s)*(2*Y.birth.port+3*observedBookBodyWidth par w Y+81)

theorem exact_book_size_uses_r64_paths :
    Y.birth.native.physical.raw.length=2*c.edges := by
  let I := Y.input
  have indexed := congrArg (fun A : Σ j,PhysicalFile T (par.ticket w) j=>A.2.order.length)
    (J6R48RawRoute.compileOccurrence_native_file I)
  have half := J6R64.BootSeats.actual_native_halfport_count I
  have size : Y.birth.native.physical.order.length=2*c.edges := indexed.trans half
  let H := Y.birth.native.physical
  change H.raw.length=2*c.edges
  rw [H.source,List.length_map]
  exact size

theorem zero_book_has_source_sized_fee (zero : (par.ticket w).child.edges=0) :
    (storedBook Y).steps+3≤zeroBookSetup par w Y := by
  let port := Y.birth.port
  let U := observedBookBodyWidth par w Y
  let H := Y.birth.native.physical
  have bodies := sum_map_cap H.raw rowScanFee (2*port+3*U+81)
    (fun a used=>by
      have h := current_record_le_observedMax (fun z=>z.body.length) H.raw a used
      change a.body.length≤U at h
      unfold rowScanFee
      omega)
  have cnt : H.raw.length=2*c.edges := exact_book_size_uses_r64_paths par w Y
  have parent := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable par
  have bnd : (H.raw.map rowScanFee).sum≤2*(C*s)*(2*port+3*U+81) := by
    rw [cnt] at bodies
    exact bodies.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ parent))
  have book := (stored_book_actual Y).2.2
  change (storedBook Y).steps≤7+(H.raw.map rowScanFee).sum+((par.ticket w).child.edges)*(4*port+5) at book
  rw [zero,Nat.zero_mul,Nat.add_zero] at book
  change (storedBook Y).steps+3≤10+2*(C*s)*(2*port+3*U+81)
  omega
end ZeroBook

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)

def rootLiteralBill (B : Bank) : ℕ :=
  let path : Path sel ext ext := .root
  prepriced (sourceLeafTape X pad (machineInputs X pad M) basePos path ord) (T.frame path.reached) B

theorem actual_root_run_has_printed_leaf_factor
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (stop : (ext).edges≤(SP).cutoff) :
    let path : Path sel ext ext := .root
    (readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) B path stop).steps≤
      2^H*(rootLiteralBill X M basePos ord B+sourceArithmetic s C (ext)) := by
  let path : Path sel ext ext := .root
  let D := sourceLeafTape X pad (machineInputs X pad M) basePos path ord
  let F := T.frame path.reached
  have hw := actual_leaf_field_width_and_vertices (T:=T) path
  have n : D.rows.length=vertexCount (ext).host :=
    canonical_tape_rows (planEdges (T:=T) path)
      (fun u=>(sourceLeafRow X pad (machineInputs X pad M) basePos path ord u).code)
  have h := (literal_leaf_all_orders X pad (machineInputs X pad M) basePos path ord B rootLive).2
  have vbound : D.rows.length≤vertexCount (ext).host+4*(C*s) := n.trans_le hw.2.2
  change (runTape D X.hf F T.vPositive B).steps≤_
  exact h.trans (raw_leaf_fee_from_dimensions F.hp hw.1.le le_rfl hw.2.1 stop vbound)

variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

def zeroLiteralBill (B : Bank) : ℕ :=
  let Y := sourceState M p w
  let path := Path.step p w
  let D := sourceLeafTape X pad (machineInputs X pad M) basePos path
    (actualEdgeOrder T (p.ticket w) Y.birth.native.physical)
  prepriced D (T.frame path.reached) (stackBank (borns M) B path)

theorem actual_zero_leaf_pays_true_book_and_one_assignment
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (valid : ReadyOnStack (borns M) B)
    (stop : ((Plan sel).child c w).edges≤(SP).cutoff) (zero : ((Plan sel).child c w).edges=0) :
    (readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) B (Path.step p w) stop).steps≤
      zeroBookSetup p w (sourceState M p w)+zeroLiteralBill X M basePos p w B+sourceArithmetic s C (ext) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let path := Path.step p w
  let Y := sourceState M p w
  let bank := stackBank (borns M) B path
  let F := T.frame path.reached
  let eOrd := actualEdgeOrder T (p.ticket w) Y.birth.native.physical
  let D := sourceLeafTape X pad (machineInputs X pad M) basePos path eOrd
  have Hsame : stackBank (borns R) B path=bank :=
    congrArg (fun A : Births T key prec tw bw (pageKeyWidth m+pad)=>stackBank A B path)
      (paid_owner_leaf_keeps_births X M basePos ord ownerInputs)
  have running : opened (borns M) (IsLive (X.seed pad)) path bank :=
    stack_is_opened (borns M) B (IsLive (X.seed pad)) (live_monotone (X.seed pad)) rootLive valid path
  have hw := actual_leaf_field_width_and_vertices (T:=T) path
  have n : D.rows.length=vertexCount ((Plan sel).child c w).host :=
    canonical_tape_rows (planEdges (T:=T) path)
      (fun u=>(sourceLeafRow X pad (machineInputs X pad M) basePos path eOrd u).code)
  have h := (literal_leaf_all_orders X pad (machineInputs X pad M) basePos path eOrd bank running).2
  have vbound : D.rows.length≤vertexCount (ext).host+4*(C*s) := n.trans_le hw.2.2
  have leafEval : (runTape D X.hf F T.vPositive bank).steps≤
      zeroLiteralBill X M basePos p w B+sourceArithmetic s C (ext) := by
    let bill := prepriced D F bank
    apply h.trans
    change rawLeafCap F.words.length ell ((Plan sel).child c w).prec ((Plan sel).child c w).edges
      D.rows.length bill F.hp≤bill+sourceArithmetic s C (ext)
    have eqq : rawLeafCap F.words.length ell ((Plan sel).child c w).prec ((Plan sel).child c w).edges
        D.rows.length bill F.hp =
      rawLeafCap F.words.length ell ((Plan sel).child c w).prec 0 D.rows.length bill F.hp :=
      congrArg (fun e=>rawLeafCap F.words.length ell ((Plan sel).child c w).prec e D.rows.length bill F.hp) zero
    rw [eqq]
    exact zero_edge_fee_from_dimensions F.hp hw.1.le le_rfl hw.2.1 vbound
  have books : (storedBook Y).steps+3≤zeroBookSetup p w Y := zero_book_has_source_sized_fee p w Y zero
  change (R.leafAfter p w (sourceState R p w) stop (stackBank (borns R) B path)).steps≤_
  rw [Hsame,paid_owner_leaf_keeps_actual_source X M basePos ord ownerInputs p w]
  simp only [R,withPaidOwnerLeaves,if_pos zero]
  change (storedBook Y).steps+(runTape D X.hf F T.vPositive bank).steps+3≤
    zeroBookSetup p w Y+zeroLiteralBill X M basePos p w B+sourceArithmetic s C (ext)
  omega

#print axioms sourceArithmetic
#print axioms exact_book_size_uses_r64_paths
#print axioms zero_book_has_source_sized_fee
#print axioms actual_root_run_has_printed_leaf_factor
#print axioms actual_zero_leaf_pays_true_book_and_one_assignment
end
end J6R65LeafRate
