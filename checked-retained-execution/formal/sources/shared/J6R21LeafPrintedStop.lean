
import J6R21LeafPhysical
import J6R12BlueprintReach
import J6R21LeafWidth

/-! The serial leaf is the actual stopping branch of the R12 printed
recursive program. The word used for every sum/product is the live
call's current U/V word; there is no high-precision integer table sum
built as an unpriced intermediate. -/
namespace J6R21Leaf
open scoped Classical Polynomial BigOperators
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime AOracleCoordinates
open J6ActiveRun J6R9Recursive J6R10Repack J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8300000

variable {p ell : ℕ} {fw : List (A1R10.Word p)}

theorem readProduct_mapped (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell)
    {U V : Type} (f : U→V) (query : V→List Bool→Meter (UVBlock fw ell))
    (nodes : List U) (bits : List Bool) :
    readProduct hp he hℓ (nodes.map f) query bits =
      readProduct hp he hℓ nodes (query∘f) bits := by
  induction nodes with
  | nil => rfl
  | cons u us ih =>
    change mulM hp (query (f u) bits) (readProduct hp he hℓ (us.map f) query bits) =
      mulM hp (query (f u) bits) (readProduct hp he hℓ us (query∘f) bits)
    rw [ih]

theorem leafCompute_mapped (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell)
    (edges : ℕ) {U V : Type} (f : U→V)
    (query : V→List Bool→Meter (UVBlock fw ell)) (nodes : List U) :
    leafCompute hp he hℓ edges (nodes.map f) query =
      leafCompute hp he hℓ edges nodes (query∘f) := by
  unfold leafCompute
  congr 1
  funext bits
  exact readProduct_mapped hp he hℓ f query nodes bits

theorem actual_leaf_is_printed_stop {f : ℤ[X]} {s : ℕ}
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (r c : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N sel) (Childs sel) r)]
    (leaf : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (hp : 0<c.prec) {fw : List (A1R10.Word c.prec)} (he : 0<fw.length) (hℓ : 0<ell)
    (hPoly : Modulus c.prec hp fw=NativeProbeRing.liftPoly c.prec f)
    (edgeCount : c.host.edgeCount=c.edges)
    (nodes : List (c.host.Row⊕c.host.Col)) (hn : nodes.Nodup)
    (hall : ∀ v : c.host.Row⊕c.host.Col,v∈nodes)
    (query : (c.host.Row⊕c.host.Col)→List Bool→Meter (UVBlock fw ell))
    (hquery : ∀ (x : Fin c.edges→Bool) v,
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (query v (List.ofFn x)).result)=
        (c.host.file v).read hf c.prec
          (assignment c.host.network (x∘c.host.edgeOrder c.edges edgeCount) v)) :
    J6R18ChildWrite.castBox hPoly (uvRead hp fw ell
      (leafCompute hp he hℓ c.edges nodes query).result) = (sourceBlueprint sel r hf).program.run c := by
  let B := sourceBlueprint sel r hf
  rw [actual_leaf_exact c hp he hℓ hPoly hf edgeCount nodes hn hall query hquery]
  have spec : B.entries=physicalEntries hf := rfl
  have hc : c.edges≤(paddedShape (N sel) (Childs sel) r).cutoff := leaf
  change _=B.program.run c
  rw [Program.run,dif_pos hc]
  change _=B.leaf c
  rw [Blueprint.leaf_exact,physicalBlueprint_truth hf B spec c edgeCount]

/-- Symbolic work above the original per-read costs, in the exact
printed leaf dimensions.  The two spare terms make a simple bound
usable when every read is known to cost at most U. -/
def callLeafFee (e ell p m v U : ℕ) (hp : 0<p) : ℕ :=
  2^m*(v*(U+mulCap e ell p+2)+uvWidth e ell p+reverseFee m+innerFee e ell p hp)

theorem leaf_compute_uniform_fee (hp : 0<p) (he : 0<fw.length) (hℓ : 0<ell)
    (m : ℕ) {V : Type} (nodes : List V)
    (query : V→List Bool→Meter (UVBlock fw ell)) (U : ℕ)
    (hU : ∀ (x : Fin m→Bool) v, v∈nodes → (query v (List.ofFn x)).steps≤U) :
    (leafCompute hp he hℓ m nodes query).steps≤callLeafFee fw.length ell p m nodes.length U hp := by
  have H := (leafCompute_bills_every_entry hp he hℓ m nodes query).2
  have per (x : Fin m→Bool) : thisVertexBill nodes query (List.ofFn x)≤nodes.length*U :=
    A1R9.sum_map_le_length _ _ U (fun v h => hU x v h)
  have fee : leafEntryBill m nodes query≤2^m*(nodes.length*U) := by
    have h := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin m→Bool))) (fun x _ => per x)
    have hn : Fintype.card (Fin m→Bool)=2^m := by simp
    simpa only [leafEntryBill,Finset.sum_const,Finset.card_univ,hn,nsmul_eq_mul] using h
  have a := Nat.mul_le_mul_right (innerFee fw.length ell p hp) (Nat.sub_le (2^m) 1)
  unfold callLeafFee
  simp only [Nat.mul_add]
  simp only [Nat.mul_add] at H
  omega

theorem leaf_given_cutoff_assignments (m cutoff : ℕ) (h : m≤cutoff) :
    (∑ _ : Fin m→Bool, (1:ℕ))≤2^cutoff := by
  rw [leaf_assignment_count]
  exact Nat.pow_le_pow_right (by decide) h

#print axioms readProduct_mapped
#print axioms leafCompute_mapped
#print axioms actual_leaf_is_printed_stop
#print axioms leaf_compute_uniform_fee
#print axioms leaf_given_cutoff_assignments
end J6R21Leaf
