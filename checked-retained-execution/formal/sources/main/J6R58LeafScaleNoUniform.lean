import J6R58LeafScaleExtraLines
import J6R57LeafCapRoster

/-! The R57 static prefactor itself is unbounded in the unguarded
resident-line ABI, even though adding irrelevant lines preserves the
checked physical source command. No field width is changed. -/
namespace J6R58LeafScale
open scoped Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 J6R22Active
open J6R15ModeCost J6R21Ancestor J6R33StatefulArithmeticPage
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R50SourceProducer J6R48Leaf J6R50Leaf J6R51Leaf J6R57LeafCap
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 23500000
set_option maxRecDepth 4350

theorem generated_row_prep_cap_pays_all_unused_fields {N own w key prec page : ℕ}
    (b : ℕ) (owner : J6R15ModeCost.Word own) (unused : ResidentPort own w)
    (miss : owner≠unused.address) (lines : List (ResidentPort own w)) (n : ℕ)
    (table : OriginTable own w key prec page)
    (id : J6R15ModeCost.Word key) (p : J6R15ModeCost.Word page) (ticks : ℕ) (wires : List WireRead) :
    rowSyntaxBuildFee b (addUnused unused n lines) table owner
      (PageReadCode.generated (edges:=N) id p ticks wires)=
      rowSyntaxBuildFee b lines table owner (PageReadCode.generated (edges:=N) id p ticks wires)+
        n*(10*own+11) := by
  have h := congrArg Meter.steps (actual_collect_incoming_pays_unused_lines owner unused miss lines n)
  dsimp only at h
  rw [(collect_incoming_exact owner (addUnused unused n lines)).2,
    (collect_incoming_exact owner lines).2] at h
  unfold rowSyntaxBuildFee pageBuildFee
  dsimp only
  omega

private theorem list_item_le_sum {A : Type*} (f : A→ℕ) {x : A} {xs : List A}
    (inList : x∈xs) : f x≤(xs.map f).sum := by
  induction xs with
  | nil => cases inList
  | cons y ys ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp inList with eq|rest
    · rw [eq]
      exact Nat.le_add_right _ _
    · exact (ih rest).trans (Nat.le_add_left _ _)

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def padLeafData (site : StoredSite T v key prec tw bw page) (D : ResidentLeafData site)
    (unused : ResidentPort D.own site.birth.port) (n : ℕ) : ResidentLeafData site :=
  { D with lines := addUnused unused n D.lines }

theorem actual_stored_prefactor_unbounded_at_fixed_dimensions
    (site : StoredSite T v key prec tw bw page) (data : ResidentLeafData site)
    (F : Frame f v.child.prec) (B : PageBank f ell key prec tw bw page)
    (tape : RawTape v.child key page) (positive : 0<v.child.edges)
    (unused : ResidentPort data.own site.birth.port)
    (owner : J6R15ModeCost.Word data.own) (miss : owner≠unused.address)
    (vertex : v.child.host.Row⊕v.child.host.Col)
    (id : J6R15ModeCost.Word key) (p : J6R15ModeCost.Word page) (ticks : ℕ) (wires : List WireRead)
    (used : ((vertex, PageReadCode.generated (edges:=v.child.edges) id p ticks wires),owner)∈
      tape.rows.zip data.roster) (bound : ℕ) :
    bound<storedLeafInputScale site (fun _=>padLeafData site data unused (bound+1)) F B tape := by
  let new := padLeafData site data unused (bound+1)
  let item := ((vertex, PageReadCode.generated (edges:=v.child.edges) id p ticks wires),owner)
  let localFee := rowSyntaxBuildFee v.child.edges new.lines new.table owner item.1.2
  have shown : item∈tape.rows.zip new.roster := used
  have acc := list_item_le_sum (fun x=>rowSyntaxBuildFee v.child.edges new.lines new.table x.2 x.1.2+7) shown
  have acc' : localFee+7≤footprintExistingRows site (fun _=>new) tape := by
    unfold footprintExistingRows
    rw [if_neg (Nat.ne_of_gt positive)]
    exact acc
  have size : bound+1≤localFee := by
    change bound+1≤rowSyntaxBuildFee _ (addUnused unused (bound+1) data.lines) data.table owner _
    rw [generated_row_prep_cap_pays_all_unused_fields _ owner unused miss]
    have h : bound+1≤(bound+1)*(10*data.own+11) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact h.trans (Nat.le_add_left _ _)
  unfold storedLeafInputScale
  change bound< bookShapeFee site+4*v.child.edges+18+footprintExistingRows site (fun _=>new) tape+_
  omega

#print axioms generated_row_prep_cap_pays_all_unused_fields
#print axioms padLeafData
#print axioms actual_stored_prefactor_unbounded_at_fixed_dimensions
end
end J6R58LeafScale
