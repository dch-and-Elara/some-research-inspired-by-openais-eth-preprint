import J6R49SourceLayoutFrames
import J6R48RawRouteOccurrence

/-! The canonical page-key roster is already present at the genuine
preceding occurrence: it is the complete bank published by its
literal all-page compiler. The following scan reads its fixed-width
keys once, including those pages that have no retained child edge. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate J6R34RootAtlas
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
open J6R32ChildResidentTransfer J6R33GeneratedChildSite
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3000
set_option maxHeartbeats 7700000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

def readBankKeys {k : ℕ} {A : Type*} : List (RefRow k A) → Meter (List (Word k))
  | []=>⟨[],3⟩
  | x::xs=>
    let w := copyFixed x.address
    let r := readBankKeys xs
    ⟨w.result::r.result,w.steps+r.steps+6⟩

theorem read_bank_keys_exact {k : ℕ} {A : Type*} (bank : List (RefRow k A)) :
    readBankKeys bank=⟨bank.map RefRow.address,3+(3*k+7)*bank.length⟩ := by
  induction bank with
  | nil => simp [readBankKeys]
  | cons r rs ih =>
    simp only [readBankKeys,copy_fixed_exact,ih,List.map_cons,List.length_cons,Nat.mul_succ]
    congr 1
    omega

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.parent.depth)
local notation "P" => packing sel (ticketReady T v)

theorem transport_banked_key_order {a b : ℕ} (same : a=b)
    (native : Birth T v key prec tw bw a) :
    (same ▸ native : Birth T v key prec tw bw b).rows.map RefRow.address=
      (native.rows.map RefRow.address).map (fun w=>(same ▸ w : Word b)) := by
  cases same
  simp

def occurrencePageWord (I : OccurrenceInput T v key prec tw bw page)
    (k : PageAt T v) : Word page :=
  I.width ▸ childPageKey (I.q-A) k

theorem compiled_occurrence_has_full_ordered_keys
    (I : OccurrenceInput T v key prec tw bw page) :
    let B := compileOccurrence I
    let out := readBankKeys B.rows
    out.result=(orderedChildPages A (P).copies).map (occurrencePageWord I) ∧
      out.result.Nodup ∧ out.steps=3+(3*page+7)*B.rows.length := by
  classical
  let atlas := Classical.choice (occurrence_real_receipt I)
  let issued := A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let N := issuedBirth I.native.result issued I.words.result I.hOld atlas
  let B := compileOccurrence I
  let bank := readBankKeys B.rows
  have h : B.rows.map RefRow.address=
      (N.rows.map RefRow.address).map (fun w=>(I.width ▸ w : Word page)) :=
    transport_banked_key_order I.width N
  have ord : N.rows.map RefRow.address=
      (orderedChildPages A (P).copies).map (childPageKey (I.q-A)) := by
    change atlas.bank.map RefRow.address=_
    rw [atlas.order,List.map_map]
    rfl
  change bank.result=(orderedChildPages A (P).copies).map (occurrencePageWord I) ∧
    bank.result.Nodup ∧ bank.steps=_
  rw [show bank=⟨B.rows.map RefRow.address,3+(3*page+7)*B.rows.length⟩ from read_bank_keys_exact B.rows]
  constructor
  · change B.rows.map RefRow.address=_
    rw [h,ord,List.map_map]
    rfl
  · exact ⟨B.keysUnique,rfl⟩

theorem occurrence_page_word_injective (I : OccurrenceInput T v key prec tw bw page) :
    Function.Injective (occurrencePageWord I) := by
  have main := compiled_occurrence_has_full_ordered_keys I
  dsimp only at main
  have nd := main.2.1
  rw [main.1] at nd
  intro x y h
  exact List.inj_on_of_nodup_map nd
    ((child_pages_complete A (P).copies).2.1 x) ((child_pages_complete A (P).copies).2.1 y) h

#print axioms read_bank_keys_exact
#print axioms transport_banked_key_order
#print axioms compiled_occurrence_has_full_ordered_keys
#print axioms occurrence_page_word_injective
end
end J6R49SourceLayout