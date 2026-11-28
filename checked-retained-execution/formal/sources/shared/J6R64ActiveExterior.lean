import J6R64ActiveIncoming
import J6R34RootAtlasStable

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14500000
set_option maxRecDepth 3300
set_option Elab.async false

/-! The actual depth-one exterior begins with its marked R34 header,
not with any outgoing Plan ticket of the exterior call. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R33StatefulArithmeticPage J6R63Active J6R24MeteredRecursion J6R27PrescribedProbe
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6ActiveRun J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R14ZeroMode J6R27OriginalGate J6R25PreparedSupply J6R10Repack J6R9Recursive
open J6R32StatefulArithmetic J6R30GeneratedRootLayout J6R11Repack J6R12Repack

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co e edgew tc tj key prec tw bw page : ℕ}
variable (X : StableExterior G ell q ro co e edgew tc tj key prec tw bw)

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Offset" => (externalAddrWidth tc tj 0)

theorem read_literal_header {pw ew dep : ℕ}
    (front tail : List Bool) (p : Word pw) (d : Word dep) (m : Word ew) :
    readCallWords pw ew dep front.length
      (front++childHeaderBytes p d m tail)=
      ⟨some (p,m),callReadFee pw ew dep front.length⟩ := by
  let middle := front++p.bits++d.bits
  have size : middle.length=front.length+pw+dep := by
    simp only [middle,List.length_append,p.size,d.size]
  have hp : loadAt pw front.length (front++childHeaderBytes p d m tail)=
      ⟨some p,headerReadFee pw front.length⟩ := by
    simpa only [childHeaderBytes,List.append_assoc] using
      (load_at_boundary front p (d.bits++m.bits++tail))
  have hm : loadAt ew (front.length+pw+dep) (front++childHeaderBytes p d m tail)=
      ⟨some m,headerReadFee ew (front.length+pw+dep)⟩ := by
    simp only [←size]
    have e : front++childHeaderBytes p d m tail=middle++m.bits++tail := by
      simp only [middle,childHeaderBytes,List.append_assoc]
    rw [e]
    exact load_at_boundary middle m tail
  unfold readCallWords callReadFee
  rw [hp,hm]
  rfl

set_option maxHeartbeats 8500000 in
theorem exterior_literal_shape :
    ∃ tail : List Bool, X.header.result.bytes=X.address.marked.bytes++
      childHeaderBytes X.birth (word (q:=1) (Ext).depth) (word (q:=edgew) (Ext).edges) tail := by
  let P := (makeTypedRootParent G X.source ell X.centre).result
  have centre : (X.address.centre.val:ℤ)=(G.centre ell X.centre).val := by
    rw [X.timeOK,(odd_site_matches_geometry G ell X.centre).2.2.1]
  have precision : X.birth.val=registerPrecision (rootParams f ell m native)
      (physicalRootCall f ell base m (printedHalf m) n plant (J6R28GeneratedRootFrame.constantRootWord m))
      (G.centre ell X.centre) := X.birthOK.trans (G.precision ell X.centre).symm
  have e := true_occurrence_header (G.selector ell) (G.ready ell) (G.centre ell X.centre)
    P (rootPreset G ell) X.sample X.group X.address centre X.sampleOK X.groupOK X.issue
    X.birth precision (word (q:=1) 0) (by rfl) (by decide) (show (1:ℕ)<2 by decide) X.edgePos X.edgeFit
  let Y := ((P.physicalSelected X.group).map P.record).flatMap rowBytes
  refine ⟨Y,?_⟩
  change (makeOccurrence (b:=edgew) X.address X.birth (word (q:=1) 0) P.raw X.issue).result.bytes=_
  rw [e.2.1,no_page_in_outer_header X.address]

theorem actual_exterior_call_words (raw : List Bool) (auth : raw=X.header.result.bytes) :
    readCallWords prec edgew 1 Offset raw=
      ⟨some (X.birth,word (Ext).edges),callReadFee prec edgew 1 Offset⟩ ∧
    X.birth.val=(Ext).prec ∧ (word (q:=edgew) (Ext).edges).val=(Ext).edges := by
  obtain ⟨tail,layout⟩ := exterior_literal_shape X
  have phy := read_literal_header X.address.marked.bytes tail X.birth
    (word (q:=1) (Ext).depth) (word (q:=edgew) (Ext).edges)
  rw [external_address_width] at phy
  refine ⟨?_,(stable_exterior_header X).2.2,word_val X.edgeFit⟩
  rw [auth,layout]
  exact phy

def readExterior (B : PageBank f ell key prec tw bw page)
    (own : OwnsHeader X.header.result B) : Meter (CallWords Ext prec edgew) :=
  let raw := borrowHeader B
  have auth : raw.result=X.header.result.bytes := by
    have E : raw=⟨X.header.result.bytes,3⟩ := borrow_exact_live_header _ _ own
    rw [E]
  let out := readCallWords prec edgew 1 Offset raw.result
  have receipt := actual_exterior_call_words X raw.result auth
  let words : Word prec×Word edgew := (X.birth,word (Ext).edges)
  have readEq : out=⟨some words,callReadFee prec edgew 1 Offset⟩ := receipt.1
  have hit : out.result.isSome := by rw [readEq]; rfl
  let pair := J6R52CacheSource.unwrapSuccess out hit
  have val : pair.result=words := by
    have eq : out.result=some words := congrArg (fun W : Meter (Option (Word prec×Word edgew))=>W.result) readEq
    have E : pair=⟨words,out.steps⟩ := J6R52CacheSource.unwrap_success_exact out hit words eq
    exact congrArg (fun W : Meter (Word prec×Word edgew)=>W.result) E
  ⟨⟨pair.result.1,pair.result.2,(congrArg (fun p : Word prec×Word edgew=>p.1.val) val).trans receipt.2.1,
    (congrArg (fun p : Word prec×Word edgew=>p.2.val) val).trans receipt.2.2⟩,
    raw.steps+pair.steps+2⟩

theorem paid_actual_exterior_entry (B : PageBank f ell key prec tw bw page)
    (own : OwnsHeader X.header.result B) :
    let O := readExterior X B own
    O.result.precision.val=(Ext).prec ∧ O.result.edges.val=(Ext).edges ∧
      O.steps=callReadFee prec edgew 1 Offset+5 := by
  let O := readExterior X B own
  let raw := borrowHeader B
  have auth : raw.result=X.header.result.bytes := by
    have E : raw=⟨X.header.result.bytes,3⟩ := borrow_exact_live_header _ _ own
    rw [E]
  have receipt := actual_exterior_call_words X raw.result auth
  refine ⟨O.result.precisionValue,O.result.edgesValue,?_⟩
  have b : raw.steps=3 := congrArg Meter.steps (borrow_exact_live_header _ _ own)
  have p : (readCallWords prec edgew 1 Offset raw.result).steps=callReadFee prec edgew 1 Offset :=
    congrArg Meter.steps receipt.1
  change raw.steps+(readCallWords prec edgew 1 Offset raw.result).steps+2=_
  rw [b,p]
  omega

theorem actual_exterior_seed_receives_its_header (pad : ℕ)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (hit : ((X.seed pad).install B).result.2=true) :
    let opened := ((X.seed pad).install B).result.1
    ∃ own : OwnsHeader X.header.result opened,
      (readExterior X opened own).steps=callReadFee prec edgew 1 Offset+5 := by
  let opened := ((X.seed pad).install B).result.1
  have h : OwnsHeader X.header.result opened := successful_publish_has_exact_head (X.seed pad) B hit
  exact ⟨h,(paid_actual_exterior_entry X opened h).2.2⟩

#print axioms exterior_literal_shape
#print axioms actual_exterior_call_words
#print axioms paid_actual_exterior_entry
#print axioms actual_exterior_seed_receives_its_header
end
end J6R64Active

