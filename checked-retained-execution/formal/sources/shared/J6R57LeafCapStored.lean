import J6R57LeafCapRows
import J6R51LeafCore
import J6R48LeafExecution

/-! Bounds for the actual stored terminal dispatcher. The same physical
key book is bought once even at a zero-edge child; that child still
evaluates all scalar rows. For a positive child only the bought actual
roster and the concrete row compiler are executed, with no fallback. -/
namespace J6R57LeafCap
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R10Repack J6R21Ancestor J6R21Leaf J6R24MeteredRecursion J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34ChildPath
open J6R48Leaf J6R50Leaf J6R51Leaf J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 34000000
set_option maxRecDepth 4500
set_option linter.unusedSectionVars false
set_option Elab.async false

def rawLeafScale (e ell p M vertices bill : ℕ) (hp : 0<p) : ℕ :=
  bill+uvWidth e ell p+vertices*(mulCap e ell p+2)+reverseFee M+innerFee e ell p hp

theorem raw_leaf_cap_has_printed_factor (e ell p M vertices bill H : ℕ)
    (hp : 0<p) (stop : M≤H) :
    rawLeafCap e ell p M vertices bill hp≤2^H*rawLeafScale e ell p M vertices bill hp := by
  have tail := Nat.mul_le_mul_right (innerFee e ell p hp) (Nat.sub_le ((2:ℕ)^M) 1)
  calc
    _≤2^M*rawLeafScale e ell p M vertices bill hp := by
      unfold rawLeafCap rawLeafScale
      rw [Nat.mul_add (2^M) (bill+uvWidth e ell p+vertices*(mulCap e ell p+2)+reverseFee M)
        (innerFee e ell p hp)]
      exact Nat.add_le_add (le_refl _) tail
    _≤_ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) stop)

private theorem sum_list_mono {A : Type*} (xs : List A) (f g : A→ℕ) (h : ∀ x∈xs,f x≤g x) :
    (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih (fun y hy=>h y (List.mem_cons_of_mem _ hy)))

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "L" => (PageBank f ell key prec tw bw page)

def bookShapeFee (site : StoredSite T v key prec tw bw page) : ℕ :=
  7+(site.birth.native.physical.raw.map J6R25PreparedSupply.rowScanFee).sum+
    v.child.edges*(4*site.birth.port+5)

def storedPrepShapeFee (site : StoredSite T v key prec tw bw page)
    (data : Unit→ResidentLeafData site) (D : RawTape v.child key page)
    (name : v.child.host.Row⊕v.child.host.Col→J6R15ModeCost.Word (data ()).own) : ℕ :=
  if v.child.edges=0 then 0 else
    (D.rows.map (fun x=>rowSyntaxBuildFee v.child.edges (data ()).lines (data ()).table
      (name x.1) x.2+7)).sum

theorem actual_stored_leaf_has_structural_cap
    (site : StoredSite T v key prec tw bw page) (data : Unit→ResidentLeafData site)
    (F : Frame f v.child.prec) (pos : 0<ell) (B : L) (D : RawTape v.child key page)
    (format : HasResidentFormat D B) (H : ℕ) (stop : v.child.edges≤H)
    (name : v.child.host.Row⊕v.child.host.Col→J6R15ModeCost.Word (data ()).own)
    (checked : 0<v.child.edges→
      let keys (j : Fin v.child.edges) :=
        childKey T v site.birth.native.physical (actualEdgeOrder T v site.birth.native.physical j)
      (data ()).roster=D.rows.map (name∘Prod.fst) ∧
      ∀ x∈D.rows, SourceCommand v.child.edges keys (data ()).lines (data ()).table (name x.1) x.2) :
    let old := runTape D hf F pos B
    let out := storedLeaf site data F pos B (fun _=>old)
    out.result=old.result ∧
    out.steps≤2^H*(bookShapeFee site+4*v.child.edges+18+storedPrepShapeFee site data D name+
      rawLeafScale F.words.length ell v.child.prec v.child.edges D.rows.length (prepriced D F B) F.hp) := by
  let old := runTape D hf F pos B
  let book := storedBook site
  let rawFee := rawLeafScale F.words.length ell v.child.prec v.child.edges D.rows.length (prepriced D F B) F.hp
  let setup := bookShapeFee site+4*v.child.edges+18+storedPrepShapeFee site data D name
  have bookBound : book.steps≤bookShapeFee site := (stored_book_actual site).2.2
  have rawEval := raw_leaf_steps D hf F pos B format
  have rawBound : rawLeafCap F.words.length ell v.child.prec v.child.edges D.rows.length
      (prepriced D F B) F.hp≤2^H*rawFee :=
    raw_leaf_cap_has_printed_factor _ _ _ _ _ _ H F.hp stop
  have boot : setup≤2^H*setup := Nat.le_mul_of_pos_left _ (by positivity)
  have sum_bound : setup+2^H*rawFee≤2^H*(setup+rawFee) := by
    rw [Nat.mul_add]
    exact Nat.add_le_add_right boot _
  change (storedLeaf site data F pos B (fun _=>old)).result=old.result ∧
    (storedLeaf site data F pos B (fun _=>old)).steps≤2^H*(setup+rawFee)
  by_cases empty : v.child.edges=0
  · rw [stored_zero_preserves_read site data F pos B (fun _=>old) empty]
    refine ⟨rfl,?_⟩
    apply Nat.le_trans _ sum_bound
    change book.steps+old.steps+3≤setup+2^H*rawFee
    dsimp only [setup,storedPrepShapeFee]
    rw [if_pos empty]
    change old.steps≤_ at rawEval
    omega
  · have positive : 0<v.child.edges := Nat.pos_of_ne_zero empty
    let keyAt (j : Fin v.child.edges) :=
      childKey T v site.birth.native.physical (actualEdgeOrder T v site.birth.native.physical j)
    have hKeys : book.result=List.ofFn keyAt := (stored_book_actual site).1
    have hInj : Function.Injective keyAt :=
      (child_key_injective T v site.birth.native.physical).comp
        (actualEdgeOrder T v site.birth.native.physical).injective
    obtain ⟨roster,cmds⟩ := checked positive
    let E := data ()
    have bought : ∀ x∈D.rows,(buildOwner v.child.edges v.child.edges book.result E.lines E.table
        (name x.1)).result=some (eraseCode x.2) := by
      intro x hx
      exact real_source_command_is_bought positive book.result keyAt hInj hKeys E.lines E.table (name x.1) (cmds x hx)
    obtain ⟨out,bill⟩ := online_leaf_replays_raw hf F pos B D v.child.edges book
      (stored_book_length site) E.lines E.table name bought format
    change E.roster=D.rows.map (name∘Prod.fst) at roster
    rw [← roster] at out bill
    have paid := stored_positive_fee site data F pos B (fun _=>old) positive old.result out
    rw [paid]
    refine ⟨rfl,?_⟩
    have ownership : (D.rows.map (fun x=>(buildOwner v.child.edges v.child.edges book.result
        E.lines E.table (name x.1)).steps+7)).sum≤storedPrepShapeFee site data D name := by
      rw [storedPrepShapeFee,if_neg empty]
      exact sum_list_mono _ _ _ (fun x hx=>Nat.add_le_add_right
        (actual_owner_prep_has_literal_size_fee positive book.result keyAt hInj hKeys E.lines E.table
          (name x.1) (cmds x hx)) 7)
    apply Nat.le_trans _ sum_bound
    change (onlineLeaf hf F pos B v.child.edges v.child.edges book E.lines E.table E.roster).steps+6
      ≤setup+2^H*rawFee
    change (onlineLeaf hf F pos B v.child.edges v.child.edges book E.lines E.table E.roster).steps≤_ at bill
    dsimp only [setup]
    omega

#print axioms rawLeafScale
#print axioms raw_leaf_cap_has_printed_factor
#print axioms bookShapeFee
#print axioms storedPrepShapeFee
#print axioms actual_stored_leaf_has_structural_cap
end
end J6R57LeafCap
