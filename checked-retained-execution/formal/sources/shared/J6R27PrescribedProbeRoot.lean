
import J6R27PrescribedProbeCapacity
import J6R27PrescribedProbeRead

/-! A single immutable positive-prefix bit bank can be shared by all
printed odd centres. Occurrence reads remain metered. The suppliers
must still prepare the exact typed descendant calls on these generated
words; no subtree setup is presumed here. -/
namespace J6R27PrescribedProbe
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleMachineTimeTape J6R24MeteredRecursion
open J6R14ZeroMode J6R26StablePreparedRoot J6R11Repack J6R12Repack
open J6OrientedHost J6Mesh
set_option maxHeartbeats 4000000
set_option maxRecDepth 1500
set_option linter.unusedSectionVars false

def changeReaderWidth {f : ℤ[X]} {D n k : ℕ} {W : Prescribed f D}
    (h : n=k) (B : SuppliedProbeBits W n) : SuppliedProbeBits W k where
  read i :=
    let R := B.read i
    ⟨⟨R.result.val,R.result.property.trans h⟩,R.steps⟩
  consistent := B.consistent

theorem reader_width_is_free {f : ℤ[X]} {D n k : ℕ} {W : Prescribed f D}
    (h : n=k) (B : SuppliedProbeBits W n) (i : Fin (D+1)) :
    ((changeReaderWidth h B).read i).result.val=(B.read i).result.val ∧
    ((changeReaderWidth h B).read i).steps=(B.read i).steps :=
  ⟨rfl,rfl⟩

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {ell m l q base native width : ℕ}
variable {T : Plant V m q} {w : Fin (a m)→Fin 64}
variable (G : RootShape f m l base native width T w)
local notation "D" => externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m l q T w)
local notation "P" => J6SourcePrecision.printed m base

noncomputable abbrev rootPreset (ell : ℕ) :
    Prescribed f (externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m l q T w)) :=
  canonicalPrescribed f _ (literal_external_spare f ell m l q base native width T w G)

noncomputable def buildRootBitBank (ell : ℕ) : Meter (SuppliedProbeBits (rootPreset G ell) f.natDegree) :=
  generatedProbeBits f _ f.natDegree rfl (literal_external_spare f ell m l q base native width T w G)

theorem build_root_probe_receipt (ell : ℕ) :
    let d := externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m l q T w)
    let A := buildRootBitBank G ell
    A.steps=positiveTapeFee f.natDegree (d+1)+3 ∧
    ∀ i : Fin (d+1), (A.result.read i).result.val=encodeBits f.natDegree (i.val+1) ∧
      (A.result.read i).steps≤(d+1)*(f.natDegree+2) :=
  generated_probe_bits_receipt f _ _ rfl (literal_external_spare f ell m l q base native width T w G)

noncomputable abbrev GeneratedChildren (hf : f.Monic) (i : J6Recovery.Addr m) : Type 1 :=
  ∀ (j : Fin (D+1)) (g : Fin 64),
    @ProbePrepared f ell (physicalSize m native) 2 G.bounds hf (G.selector ell)
      (physicalRootCall f ell base m l q T w) (G.ready ell) (G.centre ell i) (rootPreset G ell) j g

noncomputable def bindLiteralInput
    (F : Frame f P) (hf : f.Monic) (i : J6Recovery.Addr m)
    (bank : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (subtrees : GeneratedChildren (ell:=ell) G hf i) :
    LiteralSite (ell:=ell) G F hf i :=
  let wEq := ((siteFrame (G.precision ell i) F).natDegree hf).symm
  ⟨rootPreset G ell,changeReaderWidth wEq bank,subtrees⟩

theorem same_bank_literal_cost
    (F : Frame f P) (hf : f.Monic) (i : J6Recovery.Addr m)
    (subtrees : GeneratedChildren (ell:=ell) G hf i) (j : Fin (D+1)) :
    let A := buildRootBitBank G ell
    let I := bindLiteralInput G F hf i A.result subtrees
    (I.2.1.read j).result.val=encodeBits f.natDegree (j.val+1) ∧
    (I.2.1.read j).steps≤(D+1)*(f.natDegree+2) :=
  (build_root_probe_receipt G ell).2 j

#print axioms reader_width_is_free
#print axioms build_root_probe_receipt
#print axioms bindLiteralInput
#print axioms same_bank_literal_cost
end J6R27PrescribedProbe
