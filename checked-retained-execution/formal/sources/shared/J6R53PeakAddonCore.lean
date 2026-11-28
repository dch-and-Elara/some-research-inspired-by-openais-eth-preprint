import J6R52CacheWholeBank
import J6R51PeakSidecar

/-! Selected encodings of the actual installed addon bank only.
The generator's raw/emitted tape and the later frame cache are
different payloads and are not counted in this observer. -/
namespace J6R53PeakAddon
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51ParentFrames J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 15500000

variable {w owner a key prec page : ℕ}
local notation "Row" => RefRow w (Addon owner a key prec page)

def indexedFixed (w owner a key prec page : ℕ) : ℕ :=
  w+owner+a+key+prec+2+page

def indexedAddonBits (x : Row) : List Bool :=
  x.address.bits++addonWords x.payload

def oldPagedRows (rows : List Row) : ℕ :=
  (rows.filter fun x=>x.payload.oldOrigin.pageKey.isSome).length

theorem indexed_addon_exact_width (x : Row) :
    (indexedAddonBits x).length=indexedFixed w owner a key prec page+
      (if x.payload.oldOrigin.pageKey.isSome then page else 0) := by
  rw [indexedAddonBits,List.length_append,x.address.size,literal_addon_width,indexedFixed]
  omega

theorem exact_installed_row_bits (rows : List Row) :
    (rows.flatMap indexedAddonBits).length=
      rows.length*indexedFixed w owner a key prec page+oldPagedRows rows*page := by
  induction rows with
  | nil => simp [oldPagedRows]
  | cons row rows ih =>
    rw [List.flatMap_cons,List.length_append,indexed_addon_exact_width,ih]
    cases f : row.payload.oldOrigin.pageKey.isSome
    · simp [oldPagedRows,f,Nat.add_mul]
      omega
    · simp [oldPagedRows,f,Nat.add_mul]
      omega

theorem indexed_rows_uniform_cap (rows : List Row) :
    (rows.flatMap indexedAddonBits).length≤rows.length*(w+addonCap owner a key prec page) := by
  apply flat_words_bound
  intro x _
  unfold indexedAddonBits
  rw [List.length_append,x.address.size]
  exact Nat.add_le_add_left (literal_addon_word_cap x.payload) _

variable {f : ℤ[X]} {ell s C tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page}

noncomputable def residentAddonPayload (bank : ResidentBank X) : List Bool :=
  bank.rows.flatMap indexedAddonBits

theorem true_resident_bank_rows (bank : ResidentBank X) : bank.rows.length=2*v.parent.edges := by
  rw [bank.exactRows]
  exact (actual_addon_tapes_count_both_half_ports X.site).2

theorem true_resident_bank_selected_fields (bank : ResidentBank X) :
    (residentAddonPayload bank).length=
      (2*v.parent.edges)*indexedFixed X.birth.port X.site.ownerWidth (dim v) key prec page+
        oldPagedRows bank.rows*page ∧
    (residentAddonPayload bank).length≤
      (2*v.parent.edges)*(X.birth.port+addonCap X.site.ownerWidth (dim v) key prec page) := by
  unfold residentAddonPayload
  have equation := exact_installed_row_bits bank.rows
  have cap := indexed_rows_uniform_cap bank.rows
  rw [true_resident_bank_rows bank] at equation cap
  exact ⟨equation,cap⟩

theorem paid_install_returns_that_same_indexed_bank (X : StoredSite T v key prec tw bw page) :
    let paid := installResidentBank X
    paid.result.rows=X.site.install.result.getD [] ∧
    paid.steps=X.site.install.steps ∧ paid.result.rows.length=2*v.parent.edges ∧
    (residentAddonPayload paid.result).length=
      (2*v.parent.edges)*indexedFixed X.birth.port X.site.ownerWidth (dim v) key prec page+
        oldPagedRows paid.result.rows*page := by
  have e := resident_install_exact X
  exact ⟨e.1,e.2,true_resident_bank_rows _,(true_resident_bank_selected_fields _).1⟩

#print axioms indexed_addon_exact_width
#print axioms exact_installed_row_bits
#print axioms indexed_rows_uniform_cap
#print axioms true_resident_bank_rows
#print axioms true_resident_bank_selected_fields
#print axioms paid_install_returns_that_same_indexed_bank
end J6R53PeakAddon
