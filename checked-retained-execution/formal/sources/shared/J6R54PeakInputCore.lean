import J6R53PeakAddonCore

/-! The concrete raw addon field of StoredSite, before its additional
address word is written into the separately installed indexed bank.
The observer is a bit serialization, not allocator metadata. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51ParentFrames J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 15500000

variable {w owner a key prec page : ℕ}
local notation "Raw" => Addon owner a key prec page
local notation "Row" => RefRow w Raw

def rawFixed (owner a key prec page : ℕ) : ℕ := owner+a+key+prec+2+page

def rawWords (xs : List Raw) : List Bool := xs.flatMap addonWords

def rawOldPagedRows (xs : List Raw) : ℕ :=
  (xs.filter (fun x=>x.oldOrigin.pageKey.isSome)).length

theorem exact_raw_addon_words (xs : List Raw) :
    (rawWords xs).length=xs.length*rawFixed owner a key prec page+rawOldPagedRows xs*page := by
  induction xs with
  | nil => simp [rawWords,rawOldPagedRows]
  | cons x xs ih =>
    change (addonWords x++rawWords xs).length=_
    rw [List.length_append,literal_addon_width,ih]
    cases pg : x.oldOrigin.pageKey.isSome
    · simp [rawOldPagedRows,rawFixed,pg,Nat.add_mul]
      omega
    · simp [rawOldPagedRows,rawFixed,pg,Nat.add_mul]
      omega

theorem uniform_raw_addon_words (xs : List Raw) :
    (rawWords xs).length≤xs.length*addonCap owner a key prec page :=
  flat_words_bound xs addonWords _ (fun x _=>literal_addon_word_cap x)

theorem indexed_adds_only_actual_address_words (rows : List Row) :
    (rows.flatMap indexedAddonBits).length=
      (rawWords (rows.map RefRow.payload)).length+rows.length*w := by
  induction rows with
  | nil => simp [rawWords]
  | cons x xs ih =>
    change (indexedAddonBits x++xs.flatMap indexedAddonBits).length=
      (addonWords x.payload++rawWords (xs.map RefRow.payload)).length+(xs.length+1)*w
    rw [indexedAddonBits,List.length_append,List.length_append,List.length_append,
      x.address.size,ih,Nat.add_mul,Nat.one_mul]
    omega

variable {f : ℤ[X]} {ell s C tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page}

noncomputable def storedRawBits (X : StoredSite T v key prec tw bw page) : List Bool :=
  rawWords X.site.input

theorem installed_payload_is_exactly_the_stored_raw_input (bank : ResidentBank X) :
    bank.rows.map RefRow.payload=X.site.input := by
  simp only [bank.exactRows,X.site.bank_exact,List.map_map,X.site.aligned,Function.comp_def]
  
theorem stored_raw_is_bounded_and_counts_true_parent_halves (X : StoredSite T v key prec tw bw page) :
    X.site.input.length=2*v.parent.edges ∧
      (storedRawBits X).length=
        (2*v.parent.edges)*rawFixed X.site.ownerWidth (dim v) key prec page+
          rawOldPagedRows X.site.input*page ∧
      (storedRawBits X).length≤(2*v.parent.edges)*addonCap X.site.ownerWidth (dim v) key prec page := by
  have length := (actual_addon_tapes_count_both_half_ports X.site).1
  have equation := exact_raw_addon_words X.site.input
  have bound := uniform_raw_addon_words X.site.input
  rw [length] at equation bound
  exact ⟨length,equation,bound⟩

theorem actual_sidecar_extra_bits_are_its_address_lane (bank : ResidentBank X) :
    (residentAddonPayload bank).length=(storedRawBits X).length+(2*v.parent.edges)*X.birth.port := by
  have h := indexed_adds_only_actual_address_words bank.rows
  rw [installed_payload_is_exactly_the_stored_raw_input bank,true_resident_bank_rows bank] at h
  exact h

theorem the_two_distinct_tapes_have_exact_pair_payload (bank : ResidentBank X) :
    (pairedAddonPayload X.site).length=(storedRawBits X).length+(residentAddonPayload bank).length := by
  unfold pairedAddonPayload storedRawBits residentAddonPayload indexedAddonBits rawWords
  rw [List.length_append,bank.exactRows]

#print axioms exact_raw_addon_words
#print axioms uniform_raw_addon_words
#print axioms indexed_adds_only_actual_address_words
#print axioms installed_payload_is_exactly_the_stored_raw_input
#print axioms stored_raw_is_bounded_and_counts_true_parent_halves
#print axioms actual_sidecar_extra_bits_are_its_address_lane
#print axioms the_two_distinct_tapes_have_exact_pair_payload
end J6R54PeakInput
