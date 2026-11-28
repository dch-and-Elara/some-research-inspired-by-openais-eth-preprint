import J6R82LayoutDebitCore
import J6R37StructuredRootCore
import J6R54ExteriorOwnerRoles

/-! Byte program for the next active layout's physical root incidence.
It does not reconstruct any entrySource value, issue a stamp, publish
an atlas or evaluate a Gate. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R27OriginalGate J6Mesh J6R49SourceLayout
open J6R54ExteriorOwner J6R14LayoutCost J6R17ModeTape

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4200000
set_option maxRecDepth 3600
set_option Elab.async false

private def asRawWord {w : ℕ} (W : A1R10.Word w) : Word w := ⟨W.val,W.property⟩

def pullPhysicalPage (m pad : ℕ) (raw : PortRow (rootHalfWidth m)) :
    Meter (Word (pageKeyWidth m+pad)) :=
  let take := cutWord (pageKeyWidth m) raw.body
  let widen := widened pad (asRawWord take.result.1)
  ⟨widen.result,take.steps+widen.steps+3⟩

def pullPageFee (m pad : ℕ) :=
  cutWordFee (pageKeyWidth m)+wideningFee (pageKeyWidth m) pad+3

theorem actual_half_row_page_field (m pad : ℕ) (side : Bool)
    (F : SeatField (a m) (pageKeyWidth m)) :
    pullPhysicalPage m pad (halfPortSpec m side F)=
      ⟨(widened pad F.page).result,pullPageFee m pad⟩ := by
  let page : A1R10.Word (pageKeyWidth m) := ⟨F.page.bits,F.page.size⟩
  have c := cutWord_exact page F.slot.bits
  have R : (halfPortSpec m side F).body=page.val++F.slot.bits := rfl
  unfold pullPhysicalPage pullPageFee
  dsimp only
  rw [R,c.1,c.2]
  dsimp only
  have eq : asRawWord page=F.page := by
    apply word_bits_inj
    rfl
  rw [eq,(widened_exact pad F.page).2]

def readHalfIncidence (m pad : ℕ) {own : ℕ}
    (book : List (RefRow (rootHalfWidth m) (Word own)))
    (row : PortRow (rootHalfWidth m)) : Meter (Option Incidence) :=
  let old := locate row.address book
  match old.result with
  | none=>⟨none,old.steps+4⟩
  | some name =>
    let take := pullPhysicalPage m pad row
    let copy := copyFixed name
    ⟨some (copy.result.bits,take.result.bits),old.steps+take.steps+copy.steps+6⟩

theorem actual_half_incidence_with_book (m pad : ℕ) {own : ℕ}
    (book : List (RefRow (rootHalfWidth m) (Word own)))
    (b : Bool) (F : SeatField (a m) (pageKeyWidth m)) (name : Word own)
    (hit : (locate (halfPortSpec m b F).address book).result=some name) :
    readHalfIncidence m pad book (halfPortSpec m b F)=
      ⟨some (name.bits,(widened pad F.page).result.bits),
        (locate (halfPortSpec m b F).address book).steps+pullPageFee m pad+(3*own+1)+6⟩ := by
  unfold readHalfIncidence
  dsimp only
  rw [hit,actual_half_row_page_field]
  dsimp only
  rw [copy_fixed_exact]

def readHalfIncidences (m pad : ℕ) {own : ℕ}
    (book : List (RefRow (rootHalfWidth m) (Word own))) :
    List (PortRow (rootHalfWidth m))→Meter (Option (List Incidence))
  | []=>⟨some [],3⟩
  | row::tail=>
    let next := readHalfIncidence m pad book row
    match next.result with
    | none=>⟨none,next.steps+4⟩
    | some cell=>
      let rest := readHalfIncidences m pad book tail
      ⟨rest.result.map (cell::·),next.steps+rest.steps+5⟩

def halfPairLimit (m pad own bookSize : ℕ) :=
  locateFee (rootHalfWidth m) bookSize+pullPageFee m pad+(3*own+1)+11

theorem actual_half_incidence_program_from_rows (m pad : ℕ) {E : Type*} {own : ℕ}
    (book : List (RefRow (rootHalfWidth m) (Word own))) (es : List E)
    (side : E→Bool) (field : E→SeatField (a m) (pageKeyWidth m))
    (old : E→Word own) (new : E→Word (pageKeyWidth m+pad))
    (hit : ∀ e,(locate (halfPortSpec m (side e) (field e)).address book).result=some (old e))
    (page : ∀ e,(widened pad (field e).page).result=new e) :
    let out := readHalfIncidences m pad book (es.map (fun e=>halfPortSpec m (side e) (field e)))
    out.result=some (es.map (fun e=>((old e).bits,(new e).bits))) ∧
      out.steps≤3+halfPairLimit m pad own book.length*es.length := by
  induction es with
  | nil => simp [readHalfIncidences]
  | cons u us ih =>
    dsimp only at ih ⊢
    rw [List.map_cons,readHalfIncidences,
      actual_half_incidence_with_book m pad book (side u) (field u) (old u) (hit u)]
    simp only [page u,ih.1,Option.map_some,List.map_cons,List.length_cons]
    refine ⟨trivial,?_⟩
    have cost := locate_bound (halfPortSpec m (side u) (field u)).address book
    unfold halfPairLimit
    rw [Nat.mul_succ]
    have h := ih.2
    unfold halfPairLimit at h
    omega

theorem actual_header_writer_width_cap {own K : ℕ} (axis : List Bool)
    (raw : List (Word own×BootRole)) (cw : own≤K) (aw : axis.length≤K) (count : raw.length≤K) :
    (emitRootHeaders axis raw).steps≤3+(19*K+85)*K := by
  have one (u : Word own×BootRole) :
      (copyFixed u.1).steps+(emitRoleGroup axis u.2).steps+6≤19*K+85 := by
    have cost := emit_role_group_cost_bound axis u.2
    rw [fit_word_fee] at cost
    rw [copy_fixed_exact]
    dsimp only
    omega
  have total (rows : List (Word own×BootRole)) : (emitRootHeaders axis rows).steps≤3+(19*K+85)*rows.length := by
    induction rows with
    | nil => simp [emitRootHeaders]
    | cons u us ih =>
      have h := one u
      cases u with
      | mk x b =>
        simp only [emitRootHeaders,List.length_cons,Nat.mul_succ]
        dsimp only at h ⊢
        omega
  exact (total raw).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ count) 3)

#print axioms actual_half_row_page_field
#print axioms actual_half_incidence_with_book
#print axioms actual_half_incidence_program_from_rows
#print axioms actual_header_writer_width_cap
end J6R94ExteriorDebit
