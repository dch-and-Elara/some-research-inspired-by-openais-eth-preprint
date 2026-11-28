import J6R54ExteriorOwnerWords

/-! Exact row-boundary continuations of the actual exterior owner
mount. Gather saves a proved-successful copied head before
recursing. Key selection creates a retained key on unwind, after
its suffix; the theorem does not reverse that scheduling. -/
namespace J6R55SelectedPeak
open scoped Polynomial
open J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R49SourceLayout
open J6R53OldOwner J6R54ExteriorOwner

set_option autoImplicit false
set_option maxRecDepth 3550
set_option maxHeartbeats 15500000

variable {own gate key prec page : ℕ}
local notation "D" => OwnerData gate key prec page

def resumeOwnerSelection (g : Word 6) (before : List (OwnerGroup own)) (tail : Meter (List (Word own))) :
    Meter (List (Word own)) :=
  before.foldr (fun h rest=>
    let cmp := cmpAddr g h.group
    if cmp.result then
      let copied := copyFixed h.key
      ⟨copied.result::rest.result,cmp.steps+rest.steps+copied.steps+3*own+12⟩
    else ⟨rest.result,cmp.steps+rest.steps+3*own+12⟩) tail

theorem actual_owner_selector_resumes_on_completed_suffix (g : Word 6)
    (before after : List (OwnerGroup own)) :
    selectOwnerKeys g (before++after)=resumeOwnerSelection g before (selectOwnerKeys g after) := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,selectOwnerKeys,resumeOwnerSelection,List.foldr_cons] at *
    rw [ih]

theorem actual_selected_key_output_contains_the_completed_suffix (g : Word 6)
    (before after : List (OwnerGroup own)) :
    (selectOwnerKeys g (before++after)).result=(selectOwnerKeys g before).result++(selectOwnerKeys g after).result := by
  simp only [select_owner_keys_exact,List.filter_append,List.map_append]

def resumeKnownOwnerCopies (copied : List (Meter D)) (tail : Meter (Option (List D))) :
    Meter (Option (List D)) :=
  copied.foldr (fun h suffix=>⟨suffix.result.map (h.result::·),h.steps+suffix.steps+4⟩) tail

theorem actual_gather_resumes_after_copied_owner_prefix {V : Type*}
    (raw : RawRoster own gate key prec page) (name : V→Word own) (value : V→D)
    (before : List V) (after : List (Word own))
    (hits : ∀ x∈before,(locate (name x) raw).result=some (value x)) :
    gatherOwners raw (before.map name++after)=
      resumeKnownOwnerCopies (before.map (fun x=>
        ⟨value x,(locate (name x) raw).steps+ownerDataFee (value x)+4⟩)) (gatherOwners raw after) := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
    have h := paid_owner_lookup_exact raw (name x) (value x) (hits x List.mem_cons_self)
    have rest := ih (fun y mem=>hits y (List.mem_cons_of_mem _ mem))
    simp only [List.map_cons,List.cons_append,gatherOwners,h,rest,resumeKnownOwnerCopies,List.foldr_cons]

def resumePageKeyCopies {page : ℕ} (heads : List (Meter (Word page))) (tail : Meter (List (Word page))) :
    Meter (List (Word page)) :=
  heads.foldr (fun h more=>⟨h.result::more.result,h.steps+more.steps+6⟩) tail

theorem actual_page_key_scan_resumes_after_paid_prefix {A : Type*} {page : ℕ}
    (before after : List (RefRow page A)) :
    readBankKeys (before++after)=
      resumePageKeyCopies (before.map (fun r=>copyFixed r.address)) (readBankKeys after) := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,List.map_cons,readBankKeys,resumePageKeyCopies,List.foldr_cons] at *
    rw [ih]

theorem exact_actual_mounted_page_read_observes_only_its_address_words
    {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    (bank : PageBank f ell key prec tw bw page) (creator : Word key)
    (entry : Stored key prec tw bw (PagedEnvelope f ell prec page))
    (same : (locate creator bank.records).result=some entry)
    (before after : PageRows entry.payload.shape ell page)
    (split : entry.payload.pages=before++after) :
    let resumed := resumePageKeyCopies (before.map (fun r=>copyFixed r.address)) (readBankKeys after)
    readMountedOwners bank creator=⟨some (entry.stamp,resumed.result),
      (locate creator bank.records).steps+resumed.steps+5⟩ := by
  unfold readMountedOwners
  dsimp only
  rw [same]
  dsimp only
  rw [split,actual_page_key_scan_resumes_after_paid_prefix]

#print axioms actual_owner_selector_resumes_on_completed_suffix
#print axioms actual_selected_key_output_contains_the_completed_suffix
#print axioms actual_gather_resumes_after_copied_owner_prefix
#print axioms actual_page_key_scan_resumes_after_paid_prefix
#print axioms exact_actual_mounted_page_read_observes_only_its_address_words
end J6R55SelectedPeak
