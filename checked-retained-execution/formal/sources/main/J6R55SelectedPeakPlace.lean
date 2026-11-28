import J6R54ExteriorOwnerWords

/-! At fresh-write and rekey boundaries, retain precisely the already
paid copies used by the original recursion. Rekey copies a new key;
the existing immutable owner payload is passed as the same value. -/
namespace J6R55SelectedPeak
open J6R26DescriptorTree
open J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R36ChildFramedRoute J6R49SourceLayout J6R53OldOwner J6R54ExteriorOwner

set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 14200000

variable {nameWidth gate key prec page : ℕ}
local notation "D" => OwnerData gate key prec page
local notation "Rows" => RawRoster nameWidth gate key prec page

def resumeFreshOwnerCopies (heads : List (Meter D)) (tail : Meter (List D)) : Meter (List D) :=
  heads.foldr (fun h suffix=>⟨h.result::suffix.result,h.steps+suffix.steps+4⟩) tail

theorem true_fresh_owner_writer_resumes_after_paid_heads
    (stamp : Stamp key prec) (before after : List (Word page)) :
    writeFreshOwners (gate:=gate) stamp (before++after)=
      resumeFreshOwnerCopies (before.map (fun p=>copyOwnerData (freshOwnerData stamp p)))
        (writeFreshOwners stamp after) := by
  induction before with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append,writeFreshOwners,List.map_cons,resumeFreshOwnerCopies,List.foldr_cons] at *
    rw [ih]

def resumeRekeyedHead (heads : List (Meter (Word nameWidth)×D)) (tail : Meter (Option Rows)) :
    Meter (Option Rows) :=
  heads.foldr (fun h suffix=>
    ⟨suffix.result.map (⟨h.1.result,h.2⟩::·),h.1.steps+suffix.steps+5⟩) tail

theorem true_rekey_resumes_after_named_address_copies
    (before : List (Word nameWidth×D)) (afterKeys : List (Word nameWidth)) (afterValues : List D) :
    setOwnerKeys (before.map Prod.fst++afterKeys) (before.map Prod.snd++afterValues)=
      resumeRekeyedHead (before.map (fun x=>(copyFixed x.1,x.2))) (setOwnerKeys afterKeys afterValues) := by
  induction before with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.cons_append,setOwnerKeys,resumeRekeyedHead,List.foldr_cons] at *
    rw [ih]

theorem successful_rekey_passes_the_exact_payload_and_copies_only_new_names
    (names : List (Word nameWidth)) (data : List D) (rows : Rows)
    (success : (setOwnerKeys names data).result=some rows) :
    rows.map RefRow.address=names ∧ rows.map RefRow.payload=data := by
  induction names generalizing data rows with
  | nil =>
    cases data with
    | nil =>
      have e : []=rows := Option.some.inj success
      subst rows
      exact ⟨rfl,rfl⟩
    | cons x xs =>
      change none=some rows at success
      contradiction
  | cons n ns ih =>
    cases data with
    | nil =>
      change none=some rows at success
      contradiction
    | cons x xs =>
      simp only [setOwnerKeys,copy_fixed_exact] at success
      cases got : (setOwnerKeys ns xs).result with
      | none => rw [got,Option.map_none] at success; contradiction
      | some rest =>
        rw [got,Option.map_some] at success
        have e : ⟨n,x⟩::rest=rows := Option.some.inj success
        subst rows
        obtain ⟨addrs,payloads⟩ := ih xs rest got
        exact ⟨congrArg (n::·) addrs,congrArg (x::·) payloads⟩

theorem write_mount_returns_only_named_old_and_new_payloads
    (s : Stamp key prec) (pageWords : List (Word page)) (old : List D)
    (destination : List (Word nameWidth)) (rows : Rows)
    (success : (writeMountedOwners s pageWords old destination).result=some rows) :
    rows.map RefRow.address=destination ∧
      rows.map RefRow.payload=old++(writeFreshOwners (gate:=gate) s pageWords).result := by
  let fresh := writeFreshOwners (gate:=gate) s pageWords
  let joined := stitchOwners fresh.result old
  change (setOwnerKeys destination joined.result).result=some rows at success
  have checked := successful_rekey_passes_the_exact_payload_and_copies_only_new_names
    destination joined.result rows success
  change rows.map RefRow.address=destination ∧ rows.map RefRow.payload=(stitchOwners fresh.result old).result at checked
  rw [stitch_owners_exact] at checked
  exact checked

#print axioms true_fresh_owner_writer_resumes_after_paid_heads
#print axioms true_rekey_resumes_after_named_address_copies
#print axioms successful_rekey_passes_the_exact_payload_and_copies_only_new_names
#print axioms write_mount_returns_only_named_old_and_new_payloads
end J6R55SelectedPeak
