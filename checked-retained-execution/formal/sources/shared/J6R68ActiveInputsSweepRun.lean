import J6R68ActiveInputsSweepEntries
import J6R66ActiveExterior

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! A thin executable replacement of only the R66 active arm. Real
boot, demand, openOnce, receipt, resident bytes and leaves are the
same source operations. No invocation of the old active fields. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R48RawRoute
open J6ActiveSchedule J6R9Recursive J6R16ModeCost J6R21Ancestor J6R48DFS
open J6R10Repack J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Here" => (Path.root : Path sel r r)

def rawStateBody (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : J→ℕ) (x : Entered T key prec tw bw page)
    (recur : (ys : Entered T key prec tw bw page) → ys.call.edges<x.call.edges → EntryOut ys) :
    EntryOut x :=
  let current := x.call
  let path := Path.step x.path x.slot
  if stop : current.edges ≤ (S).cutoff then
    let w := M.leafAfter x.path x.slot x.site stop x.bank
    ⟨(w.result,x.bank),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := readyAtPath T path active
    let A := afterPrepare M F chart x.path x.slot x.site x.bank x.owner active
    let mounted := mountResident x.site x.resident
    let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
      (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        let acquire := M.demand x.site w
        project (openOnce acquire mounted.result retire
          (fun next live bank owner =>
            recur ⟨current,path,w,next,live,bank,owner⟩ ((P).smaller current w))
          (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) x.bank))
    ⟨(out.result,x.bank),mounted.steps+A.steps+out.steps⟩

def runRawState (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T) (retire : J→ℕ)
    (x : Entered T key prec tw bw page) : EntryOut x :=
  (measure (fun y : Entered T key prec tw bw page=>y.call.edges)).wf.fix
    (rawStateBody M F chart retire) x

theorem run_raw_state_equation (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : J→ℕ) (x : Entered T key prec tw bw page) :
    runRawState M F chart retire x=rawStateBody M F chart retire x (fun y _=>runRawState M F chart retire y) := by
  exact WellFounded.fix_eq _ _ _

def runRawAfter (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : J→ℕ) (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B) :
    Meter (Block (T.frame (Path.step p u).reached) ell×L) :=
  runRawState M F chart retire ⟨c,p,u,X,resident,B,own⟩

theorem stopped_raw_after_uses_original_leaf (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B)
    (stop : ((P).child c u).edges≤(S).cutoff) :
    runRawAfter M F chart retire c p u X resident B own=
      ⟨((M.leafAfter p u X stop B).result,B),(M.leafAfter p u X stop B).steps⟩ := by
  unfold runRawAfter
  rw [run_raw_state_equation]
  dsimp only [rawStateBody]
  rw [dif_pos stop]

theorem raw_after_uses_actual_sweep (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B)
    (a : (S).cutoff<((P).child c u).edges) :
    let current := (P).child c u
    let path := Path.step p u
    let d := readyAtPath T path a
    let A := afterPrepare M F chart p u X B own a
    let mounted := mountResident X resident
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openOnce (M.demand X w) mounted.result retire
        (fun next=>runRawAfter M F chart retire current path w next)
        (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)
    let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf read
    runRawAfter M F chart retire c p u X resident B own=⟨(out.result,B),mounted.steps+A.steps+out.steps⟩ := by
  dsimp only
  change runRawState M F chart retire (⟨c,p,u,X,resident,B,own⟩ : Entered T key prec tw bw page)=_
  rw [run_raw_state_equation]
  dsimp only [rawStateBody]
  rw [dif_neg (Nat.not_le.mpr a)]
  rfl

theorem raw_after_restores (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B) :
    (runRawAfter M F chart retire c p u X resident B own).result.2=B := by
  by_cases stop : ((P).child c u).edges ≤ (S).cutoff
  · rw [stopped_raw_after_uses_original_leaf M F chart retire p u X resident B own stop]
  · rw [raw_after_uses_actual_sweep M F chart retire p u X resident B own (Nat.lt_of_not_ge stop)]

def runRawRoot (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (B : L) (own : OwnsHeader E.header B) :
    Meter (Block (T.frame (Here).reached) ell×L) :=
  if stop : r.edges ≤ (S).cutoff then
    let leaf := M.leafRoot stop B
    ⟨(leaf.result,B),leaf.steps⟩
  else
    let a := Nat.lt_of_not_ge stop
    let d := readyAtPath T Here a
    let A := rootPrepare M F chart E B own a
    let out := A.result.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive hf
      (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        project (bootWithHeader (M.initial w) retire (runRawAfter M F chart retire r Here w)
          (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) B))
    ⟨(out.result,B),A.steps+out.steps⟩

theorem raw_root_restores_actual_bank (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (B : L) (own : OwnsHeader E.header B) :
    (runRawRoot M F chart E retire B own).result.2=B := by
  by_cases stop : r.edges ≤ (S).cutoff
  · rw [runRawRoot,dif_pos stop]
  · rw [runRawRoot,dif_neg stop]


theorem raw_root_uses_actual_sweep
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (B : L) (own : OwnsHeader E.header B) (on : (S).cutoff<r.edges) :
    let d := readyAtPath T Here on
    let A := rootPrepare M F chart E B own on
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootWithHeader (M.initial w) retire (runRawAfter M F chart retire r Here w)
        (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) B)
    let out := A.result.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive hf read
    runRawRoot M F chart E retire B own=⟨(out.result,B),A.steps+out.steps⟩ := by
  dsimp only
  rw [runRawRoot,dif_neg (Nat.not_le.mpr on)]

#print axioms raw_root_uses_actual_sweep
#print axioms runRawRoot
#print axioms raw_root_restores_actual_bank

#print axioms run_raw_state_equation
#print axioms stopped_raw_after_uses_original_leaf
#print axioms runRawAfter
#print axioms raw_after_restores
#print axioms raw_after_uses_actual_sweep
end

noncomputable section
open J6Mesh J6OrientedHost J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell qr ro co e edgew tc tj key prec tw bw page s C q cw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable (X : StableExterior G ell qr ro co e edgew tc tj key prec tw bw)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Marked" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

/-- Actual marked exterior, after its one prior publication, without
  another call to the publisher or to the legacy active supplier. -/
def runRawPhysicalExterior
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X)
    (retire : J→ℕ) (B : L) (own : OwnsHeader X.header.result B) :
    Meter (Block (T.frame (Marked).reached) ell×L) :=
  runRawRoot M F chart (physicalExteriorInputs X layout) retire B own

theorem physical_exterior_sweep_uses_its_literal_header_once
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X)
    (B : L) (own : OwnsHeader X.header.result B)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff < (Ext).edges) :
    let header := readExterior X B own
    let stock := prepareStockFromHeader (s:=s) M.modeWidth header.result
    let D := rootPrepare M F chart (physicalExteriorInputs X layout) B own on
    D.result.stock=stock.result ∧
    D.steps=(callReadFee prec edgew 1 (externalAddrWidth tc tj 0)+5)+
      (layout B own on).steps+(2*cw+4*q+5)+stock.steps+4 := by
  dsimp only
  have h := actual_root_prepares_stock_from_its_one_entrance_read M F chart
    (physicalExteriorInputs X layout) B own on
  refine ⟨h.1,?_⟩
  change (rootPrepare M F chart (physicalExteriorInputs X layout) B own on).steps=_
  rw [show (rootPrepare M F chart (physicalExteriorInputs X layout) B own on).steps=
    (readExterior X B own).steps+(layout B own on).steps+(2*cw+4*q+5)+
    (prepareStockFromHeader (s:=s) M.modeWidth (readExterior X B own).result).steps+4 from h.2]
  rw [(paid_actual_exterior_entry X B own).2.2]

#print axioms runRawPhysicalExterior
#print axioms physical_exterior_sweep_uses_its_literal_header_once
end

end J6R68ActiveInputs.Sweep
