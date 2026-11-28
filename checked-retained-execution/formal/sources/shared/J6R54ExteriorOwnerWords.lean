import J6R53OldOwnerBorn
import J6R33StatefulArithmeticPageCore

/-! The paid exterior bootstrap consumes the same addressed page record that is
resident in the original occurrence bank. Whole owner headers, rather than
half-port incidence, select retained factors. All page keys are enumerated
from the whole resident atlas, including pages without incident edges. -/
namespace J6R54ExteriorOwner
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R53OldOwner J6R36ChildFramedRoute J6R26DescriptorTree
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7200000
set_option maxRecDepth 2600
set_option Elab.async false

variable {f : ℤ[X]} {ell key prec tw bw page own gate next : ℕ}

def readMountedOwners (bank : PageBank f ell key prec tw bw page) (creator : Word key) :
    Meter (Option (Stamp key prec × List (Word page))) :=
  let fetched := locate creator bank.records
  match fetched.result with
  | none => ⟨none,fetched.steps+3⟩
  | some stored =>
    let pages := readBankKeys stored.payload.pages
    ⟨some (stored.stamp,pages.result),fetched.steps+pages.steps+5⟩

theorem read_mounted_owners_exact (bank : PageBank f ell key prec tw bw page) (creator : Word key)
    (r : Stored key prec tw bw (PagedEnvelope f ell prec page))
    (same : (locate creator bank.records).result=some r) :
    readMountedOwners bank creator=⟨some (r.stamp,r.payload.pages.map RefRow.address),
      (locate creator bank.records).steps+ (3+(3*page+7)*r.payload.pages.length)+5⟩ := by
  unfold readMountedOwners
  dsimp only
  rw [same]
  dsimp only
  rw [read_bank_keys_exact]

def writeMountedOwners (stamp : Stamp key prec) (pages : List (Word page))
    (old : List (OwnerData gate key prec page)) (dest : List (Word next)) :
    Meter (Option (RawRoster next gate key prec page)) :=
  let new := writeFreshOwners (gate:=gate) stamp pages
  let args := stitchOwners new.result old
  let placed := setOwnerKeys dest args.result
  ⟨placed.result,new.steps+args.steps+placed.steps+5⟩

theorem write_mounted_owners_exact {U V : Type}
    (stamp : Stamp key prec) (pageWord : V→Word page) (oldValue : U→OwnerData gate key prec page)
    (lname : U→Word next) (rname : V→Word next) (us : List U) (vs : List V) :
    let newValue := fun k => freshOwnerData (gate:=gate) stamp (pageWord k)
    let names : U⊕V→Word next := Sum.elim lname rname
    let vals : U⊕V→OwnerData gate key prec page := Sum.elim oldValue newValue
    let order := us.map Sum.inl ++ vs.map Sum.inr
    writeMountedOwners stamp (vs.map pageWord) (us.map oldValue) (order.map names) =
      ⟨some (order.map (fun x=>⟨names x,vals x⟩)),
       (3+(vs.map (fun k=>ownerDataFee (newValue k)+4)).sum)+
       (4*us.length+3)+(3+(3*next+6)*order.length)+5⟩ := by
  dsimp only
  unfold writeMountedOwners
  rw [write_fresh_owners_exact]
  dsimp only
  rw [stitch_owners_exact]
  dsimp only
  rw [List.map_map,List.length_map]
  have combine :
      List.map oldValue us ++ List.map (freshOwnerData (gate:=gate) stamp ∘ pageWord) vs =
      (us.map Sum.inl ++ vs.map Sum.inr).map
        (Sum.elim oldValue (fun k=>freshOwnerData (gate:=gate) stamp (pageWord k))) := by
    simp only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  rw [combine,set_owner_keys_exact]
  simp only [List.map_map,Function.comp_def]

def mountWords (bank : PageBank f ell key prec tw bw page) (creator : Word key)
    (group : Word 6) (headers : List (OwnerGroup own)) (root : RawRoster own gate key prec page)
    (dest : Meter (List (Word next))) : Meter (Option (RawRoster next gate key prec page)) :=
  let sel := selectOwnerKeys group headers
  let old := gatherOwners root sel.result
  let fresh := readMountedOwners bank creator
  match old.result,fresh.result with
  | some data,some p =>
    let placed := writeMountedOwners p.1 p.2 data dest.result
    ⟨placed.result,sel.steps+old.steps+fresh.steps+dest.steps+placed.steps+8⟩
  | _,_=>⟨none,sel.steps+old.steps+fresh.steps+5⟩

theorem mount_words_from_actual_reads {U V : Type}
    (bank : PageBank f ell key prec tw bw page) (creator : Word key) (group : Word 6)
    (headers : List (OwnerGroup own)) (root : RawRoster own gate key prec page)
    (dest : Meter (List (Word next)))
    (stamp : Stamp key prec) (pageWord : V→Word page) (oldValue : U→OwnerData gate key prec page)
    (lname : U→Word next) (rname : V→Word next) (us : List U) (vs : List V)
    (oldSame : (gatherOwners root (selectOwnerKeys group headers).result).result=some (us.map oldValue))
    (pageSame : (readMountedOwners bank creator).result=some (stamp,vs.map pageWord))
    (destSame : dest.result=(us.map Sum.inl ++ vs.map Sum.inr).map (Sum.elim lname rname)) :
    let newValue := fun k=>freshOwnerData (gate:=gate) stamp (pageWord k)
    let names : U⊕V→Word next := Sum.elim lname rname
    let vals : U⊕V→OwnerData gate key prec page := Sum.elim oldValue newValue
    let order := us.map Sum.inl ++ vs.map Sum.inr
    let emit := writeMountedOwners stamp (vs.map pageWord) (us.map oldValue) dest.result
    mountWords bank creator group headers root dest=
      ⟨some (order.map (fun x=>⟨names x,vals x⟩)),
        (selectOwnerKeys group headers).steps+
        (gatherOwners root (selectOwnerKeys group headers).result).steps+
        (readMountedOwners bank creator).steps+dest.steps+emit.steps+8⟩ := by
  dsimp only
  unfold mountWords
  dsimp only
  rw [oldSame,pageSame]
  dsimp only
  have e := congrArg Meter.result (write_mounted_owners_exact stamp pageWord oldValue lname rname us vs)
  dsimp only at e
  rw [←destSame] at e
  rw [e]

#print axioms read_mounted_owners_exact
#print axioms write_mounted_owners_exact
#print axioms mount_words_from_actual_reads
end J6R54ExteriorOwner
