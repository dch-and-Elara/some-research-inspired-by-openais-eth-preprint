import J6R35GatewayPreparationShared
import J6R34RootAtlasStable

/-! A shared-input variant of the literal exterior compiler. All input
files are immutable; page compiler scans and the actual prescribed
coordinate read are repeated and charged as before. No new registry
order is assumed or taken without proof. -/
namespace J6R35GatewayPreparation
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R10
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R15ModeCost
open J6R25PreparedSupply J6R17ModeTape J6R27OriginalGate J6R18ChildWrite
open J6R34RootAtlas J6R33PageIndexedBirth J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R21Ancestor
set_option maxHeartbeats 13000000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

section Compiler
variable {f : ℤ[X]} {D p q : ℕ} {W : Prescribed f D}

def commonFromResident
    (F : Frame f p) (hf : f.Monic) (B : SuppliedProbeBits W f.natDegree)
    (m : ℕ) (ready : Resident m q) (g : Fin 64) (j : Fin (D+1)) (code : ℕ) :
    Meter (Common F.words (a m) q code (pageKeyWidth m)) :=
  let Z := outerCoordinate F hf B j
  ⟨⟨ready.axis,word g.val,word 1,ready.roster.modes,[],ready.mask,ready.seats,Z.result⟩,
      Z.steps+3*code+12⟩

def compileFromResident
    (F : Frame f p) (hf : f.Monic) (B : SuppliedProbeBits W f.natDegree)
    (m : ℕ) (hq : 0<q) (i : Fin (a m)) (fit : i.val+1≤q) (copies : J6R15ModeCost.Word q)
    (ready : Resident m q) (g : Fin 64) (j : Fin (D+1)) (code : ℕ) {ell : ℕ} (hv : 0<ell) :
    Meter (Option (List (PageRow (a m) p ell q (pageKeyWidth m) F.words i))) :=
  let raw := commonFromResident F hf B m ready g j code
  let pages := compileAtlas (w:=RootKey m) raw.result F.hp hv fit hq copies
  ⟨pages.result,raw.steps+pages.steps⟩

theorem actual_cached_atlas_compilation {r c d ell : ℕ}
    (F : Frame f p) (hf : f.Monic) (B : SuppliedProbeBits W f.natDegree)
    (m : ℕ) (hq : 0<q) (i : Fin (a m)) (fit : i.val+1≤q) (copies receive : J6R15ModeCost.Word q)
    (source : List (SignedHalfPort r c d)) (g : Fin 64) (j : Fin (D+1)) (code : ℕ) (hv : 0<ell) :
    let resident := writeResidents m hq i copies receive source
    let fresh := buildRootAtlas F hf B m hq i fit copies receive source g j code hv
    let cached := compileFromResident F hf B m hq i fit copies resident.result g j code hv
    fresh.result=cached.result ∧ fresh.steps=resident.steps+cached.steps := by
  let A := writeResidents m hq i copies receive source
  let Z := outerCoordinate F hf B j
  let R := commonFromResident F hf B m A.result g j code
  let S := compileAtlas (w:=RootKey m) R.result F.hp hv fit hq copies
  refine ⟨rfl,?_⟩
  change A.steps+Z.steps+3*code+12+S.steps=A.steps+(Z.steps+3*code+12+S.steps)
  omega

end Compiler

section Root
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)

noncomputable abbrev rootPreparationFor :=
  prepareSharedRoot G X.source ell X.field X.hq X.copies X.pre

def headerUsingShared (S : ActualRootPreparation G ell q) : Meter (DirRow key) :=
  makeOccurrence (b:=edgew) X.address X.birth (word (q:=1) 0) S.parents X.issue

def atlasUsingShared (S : ActualRootPreparation G ell q) :
    Meter (Option (List (PageRow (a m) (J6SourcePrecision.printed m base) ell q
      (pageKeyWidth m) S.frame.words (oddAxis m)))) :=
  compileFromResident S.frame X.hf S.probes m X.hq (oddAxis m) X.qFits.le
    X.copies S.resident X.group X.sample X.code X.positive

theorem shared_header_is_literal :
    let root := rootPreparationFor X
    let cached := headerUsingShared X root.result
    X.header.result=cached.result ∧
      X.header.steps=cached.steps+(makeHalfTape m [] X.source.raw).steps := by
  exact ⟨rfl,rfl⟩

theorem shared_atlas_is_literal :
    let root := rootPreparationFor X
    let cached := atlasUsingShared X root.result
    let resident := writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw
    let tape := buildRootBitBank G ell
    X.atlas.result=cached.result ∧
      X.atlas.steps=cached.steps+X.field.steps+tape.steps+resident.steps+4 := by
  let root := rootPreparationFor X
  let B := buildRootBitBank G ell
  let R := writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw
  let old := buildRootAtlas X.field.result X.hf B.result m X.hq (oddAxis m) X.qFits.le
    X.copies X.pre X.source.raw X.group X.sample X.code X.positive
  let cached := atlasUsingShared X root.result
  have h := actual_cached_atlas_compilation X.field.result X.hf B.result m X.hq (oddAxis m)
    X.qFits.le X.copies X.pre X.source.raw X.group X.sample X.code X.positive
  have same : old.result=cached.result := h.1
  have fee : old.steps=R.steps+cached.steps := h.2
  refine ⟨same,?_⟩
  change old.steps+(X.field.steps+B.steps+4)=cached.steps+X.field.steps+B.steps+R.steps+4
  omega

theorem shared_local_payload_has_source_semantics
    (k : Page (a m) (K m) (Fin 64)) :
    let root := rootPreparationFor X
    let cached := atlasUsingShared X root.result
    cached.result=some (rootTable X.chosenFields) ∧
      (locate (residentPageKey m k) (rootTable X.chosenFields)).result=some (X.chosenFields k) ∧
      J6R22Active.boxTransport X.field.result.exactMod
        (uvRead X.field.result.hp X.field.result.words ell (X.chosenFields k).probe)=
        prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell X.sample := by
  have B := Classical.choose_spec (stable_exterior_atlas X)
  exact ⟨(shared_atlas_is_literal X).1.symm.trans B.1,B.2.1 k,B.2.2 k⟩

end Root

#print axioms actual_cached_atlas_compilation
#print axioms shared_header_is_literal
#print axioms shared_atlas_is_literal
#print axioms shared_local_payload_has_source_semantics
end J6R35GatewayPreparation
