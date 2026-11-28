import J6R82LayoutDebitCore

/-! Construct the R68 ingress argument from the actual R49 predecessor
frame and live header/atlas reads. This module does not rerun packing or
change a previously selected chart. -/
namespace J6R82LayoutDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R34ChildPath J6R41StructuredAllPaths J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R48RawRoute J6R34RootAtlas
open J6R49SourceLayout J6R68ActiveInputs J6R32ChildResidentTransfer
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11500000
set_option maxRecDepth 3400
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {I : OccurrenceInput T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs (compileOccurrence I) previous)
variable (parents : ParentOwnerHeaders S) (canonical : S.pageKey=occurrencePageWord I)

local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "E" => v.child.host.Edge
local notation "R" => v.child.host.Row
local notation "D" => v.child.host.Col
local instance FintypeE : Fintype E := v.child.host.finiteEdge
local instance FintypeR : Fintype R := v.child.host.finiteRow
local instance FintypeD : Fintype D := v.child.host.finiteCol

def sameBornPageKeysInj : Function.Injective S.pageKey :=
  canonical.symm ▸ occurrence_page_word_injective I

def nativeFull64 (fit : v.child.edges<2^q) (oldInj : Function.Injective S.oldKey) :
    Full64Input v.child.host.network A :=
  let U := liveVertexKeys S parents canonical
  { format := nativeFormat S fit oldInj (sameBornPageKeysInj S canonical)
    rowExact := rfl
    colExact := rfl
    labelWidth := rfl
    order := U.result.order S
    distinct := (U.result.valid_order S).1
    complete := (U.result.valid_order S).2 }

def nativeIngress (fit : v.child.edges<2^q) (oldInj : Function.Injective S.oldKey) :
    Ingress (nativeFull64 S parents canonical fit oldInj) :=
  let U := liveVertexKeys S parents canonical
  let W := writeTargets U.result.rawRows U.result.rawCols
  let inc := sourceIncidence S
  { paid := ⟨(W.result,inc.result.getD []),U.steps+W.steps+inc.steps+5⟩
    commands := (targets_from_registered_keys S fit oldInj (sameBornPageKeysInj S canonical) U.result).1
    incidences := by
      change (sourceIncidence S).result.getD [] =
        (nativeFull64 S parents canonical fit oldInj).raw
      have good := framed_incidence_matches_format (a:=A) S fit oldInj (sameBornPageKeysInj S canonical)
      change (sourceIncidence S).result=some (nativeFull64 S parents canonical fit oldInj).raw at good
      rw [good]
      rfl }

private theorem complete_length {α : Type*} [Fintype α] (xs : List α) (nd : xs.Nodup)
    (all : ∀ x,x∈xs) : xs.length=Fintype.card α := by
  rw [←List.toFinset_card_of_nodup nd]
  have u : xs.toFinset=Finset.univ := by ext x; simp [all x]
  rw [u,Finset.card_univ]

/-- These fields constrain tangible resident lengths and word widths,
not a whole-leaf, layout, or callback fee. The old roster includes isolated
owners; its size is not inferred from the number of edges. -/
structure NativeIngressDimensions (K : ℕ) : Prop where
  owner : S.ownerWidth≤K
  port : (compileOccurrence I).port≤K
  stampKey : key≤K
  stampPrecision : prec≤K
  pageKey : page≤K
  extent : v.child.edges≤K
  parentRows : parents.raw.length≤K
  creationPages : (compileOccurrence I).rows.length≤K
  rowCount : Fintype.card R≤K
  colCount : Fintype.card D≤K
  leftBody : ∀ e : E,(frameOf S e).left.body.length≤K
  rightBody : ∀ e : E,(frameOf S e).right.body.length≤K

theorem exact_native_ingress_paid_once (fit : v.child.edges<2^q)
    (oldInj : Function.Injective S.oldKey) :
    let U := liveVertexKeys S parents canonical
    let W := writeTargets U.result.rawRows U.result.rawCols
    let inc := sourceIncidence S
    (nativeIngress S parents canonical fit oldInj).paid.steps=U.steps+W.steps+inc.steps+5 := rfl

theorem actual_descendant_ingress_fits_width_roof (fit : v.child.edges<2^q)
    (oldInj : Function.Injective S.oldKey) (K : ℕ) (bound : NativeIngressDimensions S parents K) :
    (nativeIngress S parents canonical fit oldInj).paid.steps≤ ingressRoof K := by
  let U := liveVertexKeys S parents canonical
  let W := writeTargets U.result.rawRows U.result.rawCols
  let inc := sourceIncidence S
  have lr : U.result.rows.length≤K :=
    (complete_length _ U.result.rowsUnique U.result.rowsAll).le.trans bound.rowCount
  have lc : U.result.cols.length≤K :=
    (complete_length _ U.result.colsUnique U.result.colsAll).le.trans bound.colCount
  have roster : U.steps≤(3*K+77)*K+(3*K+1)*K+(3*K+7)*K+18 := by
    have bill := (live_vertex_keys_exact S parents canonical).2.2
    change U.steps=_ at bill
    rw [bill]
    have howner := bound.owner
    have hpage := bound.pageKey
    have p := Nat.mul_le_mul (by omega : 3*S.ownerWidth+77≤3*K+77) bound.parentRows
    have r := Nat.mul_le_mul (by omega : 3*S.ownerWidth+1≤3*K+1)
      (show (liveVertexKeys S parents canonical).result.rows.length≤K from lr)
    have c := Nat.mul_le_mul (by omega : 3*page+7≤3*K+7) bound.creationPages
    -- Make the linear width hypotheses available to the arithmetic tactic.
    omega
  have commands : W.steps≤(6*K+22)*K+(3*K+13)*K+4 := by
    have native := (targets_from_registered_keys S fit oldInj
      (sameBornPageKeysInj S canonical) U.result).2
    change W.steps≤_ at native
    apply native.trans
    have howner := bound.owner
    have hpage := bound.pageKey
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.mul_le_mul (by omega : 6*S.ownerWidth+22≤6*K+22) lr)
      (Nat.mul_le_mul (by omega : 3*page+13≤3*K+13) lc)) 4
  have rows : inc.steps≤7+(33*K+67)*K := by
    have bill := congrArg Meter.steps (physical_incidence_from_frames S)
    change inc.steps=7+_ at bill
    rw [bill]
    apply Nat.add_le_add_left _ 7
    have se := sum_mapped_bounded (childOrder S) (fun e=>framedIncidenceFee (frameOf S e)+6)
      (33*K+67) (fun e _=>incidence_row_width_cap (frameOf S e) bound.port bound.owner
        bound.stampKey bound.stampPrecision bound.pageKey (bound.leftBody e) (bound.rightBody e))
    have len : (childOrder S).length=v.child.edges := by simp [childOrder]
    exact se.trans (Nat.mul_le_mul_left _ (len.le.trans bound.extent))
  change U.steps+W.steps+inc.steps+5≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add roster commands) rows) 5

/-- Transfer only by equality of the whole paid input program result,
not merely by equality of row names, incidence bytes or copy words. -/
theorem same_measured_descendant_bytes_supply_rawDebit
    (fit : v.child.edges<2^q) (oldInj : Function.Injective S.oldKey) (K : ℕ)
    (bound : NativeIngressDimensions S parents K) (paid : Meter IngressBytes)
    (actual : paid=(nativeIngress S parents canonical fit oldInj).paid) :
    paid.steps≤ ingressRoof K := by
  rw [actual]
  exact actual_descendant_ingress_fits_width_roof S parents canonical fit oldInj K bound

#print axioms nativeFull64
#print axioms nativeIngress
#print axioms exact_native_ingress_paid_once
#print axioms actual_descendant_ingress_fits_width_roof
#print axioms same_measured_descendant_bytes_supply_rawDebit
end
end J6R82LayoutDebit
