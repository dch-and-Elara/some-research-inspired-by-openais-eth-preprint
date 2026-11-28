import J6R49LeafCore
import J6R49LeafExterior
import J6R49LeafNative
import J6R35RootOriginsFrontier

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24800000
set_option maxRecDepth 3500

/-! All rows of every reached source leaf. Three proved origin cases
synthesize the previously supplied R33 leaf semantic law. The tape
is a proof-side construction from the actual typed hierarchy, not a
paid emitter or an assertion about unrelated externally supplied tapes. -/
namespace J6R49Leaf
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R24MeteredRecursion
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R15ModeCost J6R16ModeCost
open J6R30ProducedGateRegistry J6R18ChildWrite J6R19Retained J6R27OriginalGate
open J6R22Active J6R9PacketScopes J6R35RootOrigins J6R48Leaf J6R34ChildPath
open J6R9Recursive J6R10Reachable J6R21Leaf

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pageAt" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable (actual : InputFamily P key prec tw bw (pageKeyWidth m+pad))
local notation "births" => compileFamily actual
local notation "RootLive" => IsLive (X.seed pad)
local notation "BankAt" => PageBank f ell key prec tw bw pageAt

theorem source_leaf_row_exists (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (path : Path sel ext c) (ord : Fin c.edges≃c.host.Edge) (vertex : Vertex c) :
    Nonempty (RowAt X.hf (P.frame path.reached) P.vPositive ord vertex (opened births RootLive path)) := by
  let live := opened births RootLive path
  let F := P.frame path.reached
  rcases actual_path_has_full_typed_origin X pad births path vertex with old|outside|inside
  · obtain ⟨origin,⟨tr⟩⟩ := old
    exact ⟨originalRow T (J6R28GeneratedRootFrame.constantRootWord m) X.hf F P.vPositive ord vertex
      live basePos origin tr (width:=c.edges) (Nat.lt_two_pow_self (n:=c.edges)).le⟩
  · obtain ⟨k,_,⟨tr⟩⟩ := outside
    exact ⟨exteriorRow X F P.vPositive ord vertex pad k live
      (fun B alive=>opened_keeps_root X pad births path B alive) tr⟩
  · obtain ⟨anc,earlier,slot,k,on,⟨tr⟩⟩ := inside
    exact ⟨fromCompiledOccurrence P (earlier.ticket slot) (actual earlier slot) k
      path births on RootLive F P.vPositive vertex tr ord⟩

def sourceLeafRow (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (path : Path sel ext c) (ord : Fin c.edges≃c.host.Edge) (vertex : Vertex c) :
    RowAt X.hf (P.frame path.reached) P.vPositive ord vertex (opened births RootLive path) :=
  Classical.choice (source_leaf_row_exists X pad actual basePos path ord vertex)

def sourceLeafTape (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (path : Path sel ext c) (ord : Fin c.edges≃c.host.Edge) : RawTape c key pageAt :=
  PagedLeaf.toRaw (compiledLeaf (planEdges (T:=P) path)
    (sourceLeafRow X pad actual basePos path ord))

theorem literal_leaf_all_orders (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (path : Path sel ext c) (ord : Fin c.edges≃c.host.Edge)
    (B : BankAt) (running : opened births RootLive path B) :
    let F := P.frame path.reached
    let D := sourceLeafTape X pad actual basePos path ord
    let out := runTape D X.hf F P.vPositive B
    F.decode out.result=reduce c.prec f ell (c.host.contract X.hf) ∧
      out.steps≤rawLeafCap F.words.length ell c.prec c.edges D.rows.length (prepriced D F B) F.hp := by
  let F := P.frame path.reached
  let family := sourceLeafRow X pad actual basePos path ord
  let D := compiledLeaf (planEdges (T:=P) path) family
  have format := compiled_leaf_format (planEdges (T:=P) path) family B running
  have fee := raw_leaf_steps (PagedLeaf.toRaw D) X.hf F P.vPositive B format
  have e := raw_leaf_is_same_dispatch D X.hf F P.vPositive B
  exact ⟨(congrArg F.decode (congrArg Meter.result e)).trans
    (compiled_leaf_in_literal_order (planEdges (T:=P) path) family B running),fee⟩

def literalResident (basePos : 0<base) :
    PagedResident P key prec tw bw pageAt :=
  residentFromRows births RootLive (live_monotone (X.seed pad))
    (fun p _ v=>sourceLeafRow X pad actual basePos p (planOrder (T:=P) p) v)

theorem literal_resident_leaf_format (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (path : Path sel ext c) (stop : c.edges≤(SP).cutoff)
    (B : BankAt) (running : opened births RootLive path B) :
    HasResidentFormat (PagedLeaf.toRaw ((literalResident X pad actual basePos).leaf path stop)) B :=
  resident_from_rows_has_real_format births RootLive (live_monotone (X.seed pad))
    (fun p _ v=>sourceLeafRow X pad actual basePos p (planOrder (T:=P) p) v) path stop B running

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem literal_same_plan_stopping_leaf (basePos : 0<base) {c : Call (PhysicalHost f ell)}
    (path : Path sel ext c) (stop : c.edges≤(SP).cutoff)
    (B : BankAt) (running : opened births RootLive path B) :
    let R := literalResident X pad actual basePos
    let F := P.frame path.reached
    let data := PagedLeaf.toRaw (R.leaf path stop)
    let out := nativePaged R c path B
    F.decode out.result.1=(sourceBlueprint sel ext X.hf).program.run c ∧
      out.result.2=B ∧
      out.steps≤rawLeafCap F.words.length ell c.prec (SP).cutoff
        (vertexCount (ext).host+4*(ext).edges) (prepriced data F B) F.hp :=
  paid_reached_source_leaf (literalResident X pad actual basePos) path stop B running
    (literal_resident_leaf_format X pad actual basePos path stop B running)

#print axioms source_leaf_row_exists
#print axioms literal_leaf_all_orders
#print axioms literalResident
#print axioms literal_resident_leaf_format
#print axioms literal_same_plan_stopping_leaf
end
end J6R49Leaf
