import J6R33GeneratedChildSiteSparse
import J6R33PageIndexedBirthBank

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9700000

/-! Produce the shared finite packet input from the literal descendant's
paid immutable files and one incoming active event. Event vectors are
not looked up for free. A single paid lockstep scan emits the sparse
support; individual pages then use their own physically encoded keys. -/
namespace J6R33GeneratedChildSite
open scoped Classical
open AOracleMachineTime J6R21Ancestor J6R17ModeTape J6R15ModeCost J6R27OriginalGate
open J6R30ProducedGateRegistry J6R33PageIndexedBirth J6R32ChildResidentTransfer
open J6R10Repack P11FullPacking

structure ActiveWords {p : ℕ} (fw : List (A1R10.Word p)) (q tw bw : ℕ) where
  context : CentreContext tw bw
  axis : List Bool
  group : Word 6
  exponents : List (Word q)
  coordinates : {bits : List Bool // bits.length=fw.length}

def copyCoordinates {p : ℕ} {fw : List (A1R10.Word p)}
    (coord : {bits : List Bool // bits.length=fw.length}) :
    Meter {bits : List Bool // bits.length=fw.length} :=
  let v := copyBytes coord.val
  ⟨⟨v.result,by change (copyBytes coord.val).result.length=fw.length
                rw [copyBytes_exact]; exact coord.property⟩,v.steps⟩

theorem copy_coordinates_exact {p : ℕ} {fw : List (A1R10.Word p)}
    (x : {bits : List Bool // bits.length=fw.length}) :
    (copyCoordinates (fw:=fw) x)=⟨x,3*fw.length+1⟩ := by
  have e : (copyCoordinates (fw:=fw) x).result.val=x.val :=
    congrArg Meter.result (copyBytes_exact x.val)
  have h : (copyCoordinates (fw:=fw) x).steps=3*fw.length+1 := by
    change (copyBytes x.val).steps=_
    rw [copyBytes_exact,x.property]
  generalize k : copyCoordinates (fw:=fw) x = out at e h ⊢
  cases out with
  | mk got steps =>
    change got.val=x.val at e
    change steps=3*fw.length+1 at h
    rw [Subtype.ext e,h]

def prepareSite {p a q tw bw : ℕ} {fw : List (A1R10.Word p)} (code : ℕ)
    (R : ChildResidents a q) (X : ActiveWords fw (q+1) tw bw) :
    Meter (Option (CentreContext tw bw×Common fw a (q+1) code ((q-a)+13*a))) :=
  let E := emitSupport a R.raw.roster.modes X.exponents
  let t := copyContext X.context
  let i := copyBytes X.axis
  let g := copyFixed X.group
  let s := copyFixed (word (q:=code) 1)
  let z := copyCoordinates (fw:=fw) X.coordinates
  ⟨E.result.map (fun S=>⟨t.result,⟨i.result,g.result,s.result,R.raw.roster.modes,
      S,R.raw.masks,R.seats,z.result⟩⟩),
    E.steps+t.steps+i.steps+g.steps+s.steps+z.steps+12⟩

/-- The common object shares the already paid immutable R32 files.
It is manufactured once per event, not once per physical page. -/
def commonView {p a q tw bw : ℕ} {fw : List (A1R10.Word p)} (code : ℕ)
    (R : ChildResidents a q) (X : ActiveWords fw (q+1) tw bw) :
    Common fw a (q+1) code ((q-a)+13*a) :=
  ⟨X.axis,X.group,word 1,R.raw.roster.modes,
   supportSpec R.raw.roster.modes X.exponents,R.raw.masks,R.seats,X.coordinates⟩

def prepareSiteFee (a q i deg code tw bw modes : ℕ) : ℕ :=
  modes*dispatchStride a (q+1)+contextCopyFee tw bw+3*i+3*code+3*deg+38

theorem prepare_site_exact {E A B : Type} {N : Network E A B} {a q p code tw bw : ℕ}
    {P : PhysicalPacking N a (Fin 64)} {i : Fin a} {R : ChildResidents a q}
    (H : ResidentReceipt P i p R) {fw : List (A1R10.Word p)}
    (X : ActiveWords fw (q+1) tw bw) (clock : X.axis.length=i.val)
    (len : X.exponents.length=H.modes.length) :
    prepareSite code R X =
      ⟨some (X.context,commonView code R X),
        prepareSiteFee a q i.val fw.length code tw bw H.modes.length⟩ := by
  obtain ⟨res,cost⟩ := emitSupport_exact a R.raw.roster.modes X.exponents
    ((raw_roster_clock H).trans len.symm)
  unfold prepareSite
  dsimp only
  rw [res,cost,copy_context_exact,copyBytes_exact,copy_fixed_exact,copy_fixed_exact,
    copy_coordinates_exact,raw_roster_clock H,clock]
  change (⟨some (X.context,commonView code R X),_⟩ : Meter _) = _
  congr 1
  unfold prepareSiteFee
  dsimp only
  omega

#print axioms copy_coordinates_exact
#print axioms prepare_site_exact
end J6R33GeneratedChildSite
