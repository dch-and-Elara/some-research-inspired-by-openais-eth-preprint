import J6R57PublicRequestSuccess
import J6R27PrescribedProbeRoot

/-! Bind the generated catalogue to the actual compiled graph, field
and prescribed root sample words.  The same physical source site is
returned when both the address and its sample bytes pass. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 3600
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}

structure PreparedRequests
    (W : Widths m native tc tj tw edgew)
    (C : Compiled G ell q rr cc dd prec kp bw) where
  probes : SuppliedProbeBits (rootPreset G ell) f.natDegree
  rows : List (Entry C.mark m native tc tj tw)
  ordered : rows=(emitCatalogue W C.mark).result

variable (W : Widths m native tc tj tw edgew)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def prepareActualRequests (I : SharedInputs G ell q rr cc dd prec kp bw) :
    Meter (PreparedRequests W (prepareShared I).result) :=
  let C := prepareShared I
  let P := buildRootBitBank G ell
  let R := emitCatalogue W C.result.mark
  ⟨⟨P.result,R.result,rfl⟩,C.steps+P.steps+R.steps+6⟩

theorem actual_root_request_preparation (I : SharedInputs G ell q rr cc dd prec kp bw) :
    let C := prepareShared I
    let P := buildRootBitBank G ell
    let R := emitCatalogue W C.result.mark
    let D := prepareActualRequests W I
    D.result.probes=P.result ∧ D.result.rows=R.result ∧
      D.steps=C.steps+P.steps+R.steps+6 :=
  ⟨rfl,rfl,rfl⟩

variable {W}
variable (C : Compiled G ell q rr cc dd prec kp bw)
variable (D : PreparedRequests W C)

def gateSample (r : Entry C.mark m native tc tj tw) (raw : List Bool) :
    Meter (Option (Entry C.mark m native tc tj tw)) :=
  let want := D.probes.read r.coord.1.2
  let test := eqRawBits raw want.result.val
  ⟨if test.result then some r else none,want.steps+test.steps+4⟩

theorem prescribed_sample_accepted (r : Entry C.mark m native tc tj tw) (raw : List Bool) :
    (gateSample C D r raw).result.isSome ↔ raw=List.ofFn ((rootPreset G ell).word r.coord.1.2) := by
  have h := eq_raw_bits_exact raw (D.probes.read r.coord.1.2).result.val
  unfold gateSample
  dsimp only
  by_cases yes : (eqRawBits raw (D.probes.read r.coord.1.2).result.val).result=true
  · rw [if_pos yes]
    exact ⟨fun _=>(h.1.mp yes).trans (D.probes.consistent _),fun _=>rfl⟩
  · rw [if_neg yes]
    constructor
    · intro impossible
      cases impossible
    · intro eq
      exact (yes (h.1.mpr (eq.trans (D.probes.consistent _).symm))).elim

def readPublicRequest (addr : OccurrenceAddress tc tj) (raw : List Bool) :
    Meter (Option (Entry C.mark m native tc tj tw)) :=
  let Q := rawRequest C.mark addr D.rows
  match Q.result with
  | none => ⟨none,Q.steps+3⟩
  | some r =>
    let p := gateSample C D r raw
    ⟨p.result,Q.steps+p.steps+3⟩

theorem true_prescribed_address_is_found (addr : OccurrenceAddress tc tj) (x : Coordinate m native)
    (t : addr.centre.val=index m x.1.1) (j : addr.sample.val=x.1.2.val) (g : addr.group.val=x.2.val)
    (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word x.1.2)) :
    let A := rawRequest C.mark addr D.rows
    let E := (emitAt W C.mark x).result
    let S := D.probes.read x.1.2
    let Q := readPublicRequest C D addr raw
    Q.result=some E ∧
      Q.steps=A.steps+S.steps+(eqRawBits raw S.result.val).steps+7 := by
  have hit : (rawRequest C.mark addr D.rows).result=some (emitAt W C.mark x).result :=
    by rw [D.ordered]; exact (native_raw_request_hit W C.mark addr x t j g).1
  have yes : (eqRawBits raw (D.probes.read x.1.2).result.val).result=true :=
    (eq_raw_bits_exact raw (D.probes.read x.1.2).result.val).1.mpr
      (legal.trans (D.probes.consistent _).symm)
  unfold readPublicRequest gateSample
  dsimp only
  rw [hit]
  change (if (eqRawBits raw (D.probes.read x.1.2).result.val).result then some (emitAt W C.mark x).result
    else none)=some (emitAt W C.mark x).result ∧
    (rawRequest C.mark addr D.rows).steps+((D.probes.read x.1.2).steps+
      (eqRawBits raw (D.probes.read x.1.2).result.val).steps+4)+3=
    (rawRequest C.mark addr D.rows).steps+(D.probes.read x.1.2).steps+
      (eqRawBits raw (D.probes.read x.1.2).result.val).steps+7
  rw [if_pos yes]
  exact ⟨rfl,by omega⟩

def entrySource (r : Entry C.mark m native tc tj tw) :
    Meter (StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) :=
  siteFromHead W r.coord.2 C r.head

theorem entry_source_is_actual (r : Entry C.mark m native tc tj tw) :
    let X := entrySource (W:=W) C r
    X.result.source=C.literal ∧ X.result.field=⟨C.frame,0⟩ ∧
      X.result.address=r.wire ∧ X.result.issue.result=r.id ∧
      X.steps=ordinalFee 6 r.coord.2.val+8 := by
  have h := site_keeps_shared_payload W r.coord.2 C r.head
  have A : (entrySource (W:=W) C r).result.address=(realAddress r.head.data r.coord.2).result := rfl
  refine ⟨h.1,h.2.1,A.trans r.exactWire.symm,?_,site_exact_local_fee W r.coord.2 C r.head⟩
  change (issueExterior C.mark (realAddress r.head.data r.coord.2).result).result=r.id
  rw [←r.exactWire,←r.exactID]

theorem actual_prescribed_request_returns_same_source_site
    (addr : OccurrenceAddress tc tj) (x : Coordinate m native)
    (t : addr.centre.val=index m x.1.1) (j : addr.sample.val=x.1.2.val) (g : addr.group.val=x.2.val)
    (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word x.1.2)) :
    let S := readPublicRequest C D addr raw
    S.result.map (fun row=>(entrySource (W:=W) C row).result) =
      some (siteFromHead W x.2 C (prepareHead W x.1.1 x.1.2).result).result := by
  dsimp only
  rw [(true_prescribed_address_is_found C D addr x t j g raw legal).1]
  rfl

#print axioms actual_root_request_preparation
#print axioms prescribed_sample_accepted
#print axioms true_prescribed_address_is_found
#print axioms entry_source_is_actual
#print axioms actual_prescribed_request_returns_same_source_site
end
end J6R57PublicRequest
