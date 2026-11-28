import J6R33OriginalJ6QueryTape
import J6R27PrescribedProbeRoot
import J6R27PrescribedProbeBudget
import J6R26StablePreparedRootCount

/-! J6 is a counting reduction to the specified completed root-slot
oracle, not an algorithm for evaluating the oracle. Its legal inputs
are one fixed physical circuit, layout, signed odd centre, literal
binary probe and zero mode. This interface never asks for a Prepared
child or for a child-value oracle. -/
namespace J6R33OriginalJ6
open scoped Classical Polynomial BigOperators
open Polynomial A1R10 A1R11 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J6R9Recursive J6R11Repack J6R12Repack
open J6R14ZeroMode J6R22Active J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe
open J6ActiveRun J6ActiveSchedule
set_option maxHeartbeats 14000000
set_option maxRecDepth 2100
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m l q base native width : ℕ}
variable {T : Plant V m q} {w : Fin (a m)→Fin 64}
variable (G : RootShape f m l base native width T w)
local notation "p₀" => J6SourcePrecision.printed m base

abbrev SiteFrame (ell : ℕ) (F : Frame f p₀) (i : J6Recovery.Addr m) :=
  siteFrame (G.precision ell i) F

structure CompletedOracle (ell : ℕ) (F : Frame f (J6SourcePrecision.printed m base)) (hf : f.Monic) where
  reply : ∀ (i : J6Recovery.Addr m), Fin (literalDegree m native+1) →
    List Bool → Block (SiteFrame G ell F i) ell
  correct : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
      (raw : List Bool), raw=List.ofFn ((rootPreset G ell).word j) →
    (SiteFrame G ell F i).decode (reply i j raw)=
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) hf (rootPreset G ell) j

section Site
variable {ell : ℕ} {F : Frame f (J6SourcePrecision.printed m base)} {hf : f.Monic}
local notation "d₀" => literalDegree m native

/-! An exact request carries its typed odd centre and literal binary
coordinate, with beta=0 fixed by the interface. The stored indexed
odd-centre and sample tags select a legal call, not a table of presumed
answers. The meter covers traversing request/reply bits; the time spent
by the externally supplied oracle is not included. -/
def slotCommFee (e m _d ell p : ℕ) : ℕ :=
  queryFee m e+(3*(m+3)+2)+jetEntryWidth e ell p+4

def callSlot (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (O : CompletedOracle G ell F hf)
    (i : J6Recovery.Addr m) (j : Fin (d₀+1)) :
    Meter (Block (SiteFrame G ell F i) ell) :=
  let bits := A.read j
  let packet := signedQuery m i bits.result.val
  let taken := peelRequest (m+3) packet.result
  let response := O.reply i j taken.result
  ⟨response,bits.steps+packet.steps+taken.steps+jetEntryWidth f.natDegree ell p₀+4⟩

theorem actual_completed_slot (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (O : CompletedOracle G ell F hf) (i : J6Recovery.Addr m) (j : Fin (d₀+1)) :
    let R := callSlot G A O i j
    (SiteFrame G ell F i).decode R.result=
      fallbackTable (G.selector ell) (G.ready ell) (G.centre ell i) hf (rootPreset G ell) j ∧
    R.steps≤(A.read j).steps+slotCommFee f.natDegree m d₀ ell p₀ := by
  let B := A.read j
  let Q := signedQuery m i B.result.val
  let X := peelRequest (m+3) Q.result
  let E := SiteFrame G ell F i
  have data : X=⟨B.result.val,3*(m+3)+2⟩ := query_payload_exact m i B.result.val
  have price : Q.steps≤queryFee m f.natDegree := by
    have pc := (signed_query_exact m i B.result.val).2
    change Q.steps≤queryFee m B.result.val.length at pc
    rw [B.result.property] at pc
    exact pc
  constructor
  · change E.decode (O.reply i j X.result)=_
    rw [data]
    exact O.correct i j B.result.val (A.consistent j)
  · change B.steps+Q.steps+X.steps+jetEntryWidth f.natDegree ell p₀+4≤_
    rw [data]
    change B.steps+Q.steps+(3*(m+3)+2)+uvWidth f.natDegree ell p₀+4≤
      B.steps+(queryFee m f.natDegree+(3*(m+3)+2)+uvWidth f.natDegree ell p₀+4)
    omega

def siteReader (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (i : J6Recovery.Addr m) (j : Fin (d₀+1)) :
    Meter {u : List Bool // u.length=(SiteFrame G ell F i).words.length} :=
  (changeReaderWidth ((SiteFrame G ell F i).natDegree hf).symm A).read j

noncomputable def oracleSite (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (O : CompletedOracle G ell F hf) (hv : 0<ell) (i : J6Recovery.Addr m) :
    Meter (Block F ell) :=
  let E := SiteFrame G ell F i
  let R := interpolateAt0 E.hp E.sizePos hv
    (readPrescribed E.hp hv (siteReader (F:=F) (hf:=hf) G A i)) (callSlot G A O i)
  restoreFrame (G.precision ell i) F R

theorem oracle_site_exact (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (O : CompletedOracle G ell F hf) (hv : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (i : J6Recovery.Addr m) :
    let E := SiteFrame G ell F i
    let node := readPrescribed E.hp hv (siteReader (F:=F) (hf:=hf) G A i)
    let out := oracleSite G A O hv i
    F.decode out.result=
      (polynomial (stableRootPacking m l q width T w G.room G.half G.rankA G.rankFit.le)
        (oddAxis m) (index m i:ℤ) p₀ (rootEntryFile f ell base T w) hf).eval 0 ∧
    out.steps≤ interpBill node (callSlot G A O i)+
      interpExtra E.words.length ell (registerPrecision (rootParams f ell m native)
        (physicalRootCall f ell base m l q T w) (G.centre ell i)) 1 (d₀+1) E.hp+
      jetCoeffFee E.words.length ell (registerPrecision (rootParams f ell m native)
        (physicalRootCall f ell base m l q T w) (G.centre ell i)) 1+3 := by
  let E := SiteFrame G ell F i
  let pr := registerPrecision (rootParams f ell m native)
    (physicalRootCall f ell base m l q T w) (G.centre ell i)
  let W := rootPreset G ell
  let read := siteReader (F:=F) (hf:=hf) G A i
  let node := readPrescribed E.hp hv read
  let sample := callSlot G A O i
  let R := interpolateAt0 E.hp E.sizePos hv node sample
  let P := physicalZeroP (G.selector ell) (G.ready ell) (G.centre ell i) hf
  have hD := E.natDegree hf
  have hF : 0<f.natDegree := hD ▸ E.sizePos
  have H (j : Fin (d₀+1)) : (read j).result.val=List.ofFn (W.word j) := A.consistent j
  have nodes (j : Fin (d₀+1)) : boxTransport E.exactMod (nodeMeaning E.hp node j)=prescribedNode W pr ell j :=
    (read_prescribed_exact E.hp hv W E.exactMod read H j).1
  have values (j : Fin (d₀+1)) : boxTransport E.exactMod (nodeMeaning E.hp sample j)=P.eval (prescribedNode W pr ell j) :=
    (actual_completed_slot G A O i j).1.trans
       (physicalZeroP_eval (G.selector ell) (G.ready ell) (G.centre ell i)
          G.bounds (G.stable ell) hf hF (prescribedNode W pr ell j)).symm
  obtain ⟨h,fee⟩ := prescribed_interpolate_at_zero E.hp E.sizePos hv hf hF hD E.exactMod W node sample P
    (physicalZeroP_degree (G.selector ell) (G.ready ell) (G.centre ell i) hf) nodes values
  have tr := restore_frame_receipt (G.precision ell i) F R
  refine ⟨?_,?_⟩
  · change F.decode (restoreFrame (G.precision ell i) F R).result=_
    rw [tr.1]
    change E.decode R.result=P.eval 0 at h
    rw [h]
    exact physical_zero_is_stable base m l q native width T w G.room G.half G.nativeFits
      G.rankA G.rankFit.le (G.ready ell) hf i
  · change (restoreFrame (G.precision ell i) F R).steps≤_
    rw [tr.2]
    exact fee

end Site
#print axioms actual_completed_slot
#print axioms oracle_site_exact
end J6R33OriginalJ6
