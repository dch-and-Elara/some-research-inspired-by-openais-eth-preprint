import J6R49SourceLayoutDescend
import J6R49SourceLayoutPageKeys

/-! Read the required new child column keys from the preceding native
all-page Birth, not a separate page menu. The old live owner header
table still needs to cover its actual retained rows, including isolated
old factors; the rule cannot find those from incidences alone. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate J6R34RootAtlas
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
open J6R32ChildResidentTransfer
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2900
set_option maxHeartbeats 8200000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {I : OccurrenceInput T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs (compileOccurrence I) previous)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.parent.depth)
local notation "P" => packing sel (ticketReady T v)

structure OldVertexKeys (S : SiteInputs (compileOccurrence I) previous) where
  rows : List v.child.host.Row
  unique : rows.Nodup
  all : ∀ u,u∈rows
  raw : List (Word S.ownerWidth)
  exact : raw=rows.map (nativeRowKey S)

def colsOfBirth : List v.child.host.Col :=
  (orderedChildPages A (P).copies).map (physicalChildCols (T:=T) (v:=v)).symm

theorem cols_of_birth_complete :
    (colsOfBirth (T:=T) (v:=v)).Nodup ∧ ∀ x,x∈colsOfBirth (T:=T) (v:=v) := by
  let E := physicalChildCols (T:=T) (v:=v)
  let K := orderedChildPages A (P).copies
  obtain ⟨kn,ha,_⟩ := child_pages_complete A (P).copies
  change (K.map E.symm).Nodup ∧ ∀ x,x∈K.map E.symm
  exact ⟨kn.map E.symm.injective,fun x=>List.mem_map.mpr ⟨E x,ha (E x),E.symm_apply_apply x⟩⟩

theorem registered_pages_from_the_same_birth (source : S.pageKey=occurrencePageWord I) :
    (readBankKeys (compileOccurrence I).rows).result=
      (colsOfBirth (T:=T) (v:=v)).map (nativeColKey S) := by
  have K := (compiled_occurrence_has_full_ordered_keys I).1
  change (readBankKeys (compileOccurrence I).rows).result=
    (orderedChildPages A (P).copies).map (occurrencePageWord I) at K
  rw [K,colsOfBirth,List.map_map]
  apply List.map_congr_left
  intro p _
  change occurrencePageWord I p =
    S.pageKey ((physicalChildCols (T:=T) (v:=v)) ((physicalChildCols (T:=T) (v:=v)).symm p))
  rw [Equiv.apply_symm_apply,source]

def vertexKeysOfBirth (owner : OldVertexKeys S) (source : S.pageKey=occurrencePageWord I) :
    Meter (VertexKeys S) :=
  let read := readBankKeys (compileOccurrence I).rows
  ⟨⟨owner.rows,colsOfBirth (T:=T) (v:=v),owner.unique,(cols_of_birth_complete (T:=T) (v:=v)).1,
      owner.all,(cols_of_birth_complete (T:=T) (v:=v)).2,owner.raw,read.result,
      owner.exact,registered_pages_from_the_same_birth S source⟩,read.steps+4⟩

theorem exact_vertex_roster_from_actual_birth (owner : OldVertexKeys S)
    (source : S.pageKey=occurrencePageWord I) :
    let W := vertexKeysOfBirth S owner source
    W.result.rawRows=owner.raw ∧ W.result.rawCols=(readBankKeys (compileOccurrence I).rows).result ∧
      Function.Injective S.pageKey ∧ W.steps=7+(3*page+7)*(compileOccurrence I).rows.length := by
  refine ⟨rfl,rfl,source.symm ▸ occurrence_page_word_injective I,?_⟩
  change (readBankKeys (compileOccurrence I).rows).steps+4=_
  rw [read_bank_keys_exact]
  dsimp only
  omega

#print axioms cols_of_birth_complete
#print axioms registered_pages_from_the_same_birth
#print axioms exact_vertex_roster_from_actual_birth
end
end J6R49SourceLayout