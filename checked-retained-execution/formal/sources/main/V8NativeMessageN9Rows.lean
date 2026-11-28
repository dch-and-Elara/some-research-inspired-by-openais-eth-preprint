import V8NativeMessageN9
import V8NativeMessageReceive

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 3000

namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open V8PooledMenu
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G]
  [Fintype G] {a : ℕ} {N : Network E A B}

/-- The actual child bit for each tag only uses retained tables of that
child. The flag lemma is deliberately stated at its original vertices. -/
theorem childParity_local (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (flag flag' : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (tag : Option (TileForm P i))
    (locality : ∀ (u : A ⊕ B), atGroup P i u=g → ∀ q, flag u q=flag' u q) :
    childParity P i t flag g tag=childParity P i t flag' g tag := by
  unfold childParity
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 2
  unfold oldScalar
  refine Finset.prod_congr rfl (fun u _ => ?_)
  rw [locality u.val u.property]

/-- Full codomain for each party is permitted. This deliberately also
counts unused coordinates for the other party when bounding bits. -/
def fuseChildren (P : PhysicalPacking N a G) (i : Fin a) (T : Finset G)
    (row col : ChildTape P i) : ChildTape P i :=
  (fun g => if g∈T then row.1 g else col.1 g,
   fun c => if formSource P i c∈T then row.2 c else col.2 c)

omit [Fintype E] [Fintype A] [Fintype B] in
theorem childTape_nat_card (P : PhysicalPacking N a G) (i : Fin a) :
    Nat.card (ChildTape P i) = 2^childBits P i :=
  Nat.card_eq_fintype_card.trans (childTape_card P i)

namespace Five
open V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin
variable {V F : Type} [Fintype V] [Fintype F] {G₀ : Graph V F} {p : ThreePorts G₀} {f : ℤ[X]}

theorem childParity_switch_local (P : Packing G₀ p) (i : Fin (rootA V))
    (t : ℤ) (g : Fin 64) (s s' : V→Bool) (tag : Option (TileForm P i))
    (hs : ∀ v, switchGroup P i v=g → s v=s' v) :
    childParity P i t (flags G₀ p s) g tag=childParity P i t (flags G₀ p s') g tag := by
  apply childParity_local
  intro u hu q
  apply flags_only_switch
  intro v hv
  apply hs
  change atGroup P i (switchVertex v)=g
  rw [← hv]
  exact hu

variable (P : Packing G₀ p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (i : Fin (rootU V)) (T : Finset (Fin 64))

local notation "Sites" => FixedSites hu huM (rootA V) i

theorem childParity_split (t : Sites) (g : Fin 64)
    (x : RowWords P i T) (y : ColWords P i T) (tag : Option (TileForm P (rootIndex hu huM t.val))) :
    childParity P (rootIndex hu huM t.val) t.val.val (flags G₀ p (signs P i T x y)) g tag =
      if g∈T then
        childParity P (rootIndex hu huM t.val) t.val.val (flags G₀ p (rowFill P i T x)) g tag
      else childParity P (rootIndex hu huM t.val) t.val.val (flags G₀ p (colFill P i T y)) g tag := by
  split_ifs with hg
  · apply childParity_switch_local
    intro v hv
    rw [actual_index hu huM i t] at hv
    have h : switchGroup P (physIndex i) v ∈ T := hv ▸ hg
    simp only [signs,rowFill,dif_pos h]
  · apply childParity_switch_local
    intro v hv
    rw [actual_index hu huM i t] at hv
    have h : switchGroup P (physIndex i) v ∉ T := hv ▸ hg
    simp only [signs,colFill,dif_neg h]

theorem children_split (t : Sites) (x : RowWords P i T) (y : ColWords P i T) :
    encodeChildren P (rootIndex hu huM t.val) t.val.val (flags G₀ p (signs P i T x y)) =
      fuseChildren P (rootIndex hu huM t.val) T
        (encodeChildren P (rootIndex hu huM t.val) t.val.val (flags G₀ p (rowFill P i T x)))
        (encodeChildren P (rootIndex hu huM t.val) t.val.val (flags G₀ p (colFill P i T y))) := by
  apply Prod.ext
  · funext g
    exact childParity_split P hu huM i T t g x y none
  · funext c
    exact childParity_split P hu huM i T t _ x y (some c)

variable (chosen : Finset (FixedSites hu huM (rootA V) i))

abbrev RowChildTapes (selected : Finset (FixedSites hu huM (rootA V) i)) : Type :=
  (t : ↥selected) → ChildTape P (rootIndex hu huM t.val.val)

abbrev FixedChildrenMenu (chosen : Finset (FixedSites hu huM (rootA V) i)) (f : ℤ[X]) : Type :=
  (t : ↥chosen) → ChildAddress P hu huM t.val.val → Residue f 1 1

def fixedChildren (probes : Probes V f) (hf : f.Monic) (s : V→Bool) :
    FixedChildrenMenu P hu huM i chosen f :=
  fun t => actualChildMenu P hu huM t.val.val probes hf s

def rowChildren (x : RowWords P i T) : RowChildTapes P hu huM i chosen :=
  fun t => encodeChildren P (rootIndex hu huM t.val.val) t.val.val.val (flags G₀ p (rowFill P i T x))

def decodeRowChildren (row : RowChildTapes P hu huM i chosen) (y : ColWords P i T) :
    FixedChildrenMenu P hu huM i chosen f :=
  fun t => decodeNativeChildren P hu huM t.val.val
    (fuseChildren P (rootIndex hu huM t.val.val) T (row t)
      (encodeChildren P (rootIndex hu huM t.val.val) t.val.val.val (flags G₀ p (colFill P i T y))))

theorem N9_fixed_row_native (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    (x : RowWords P i T) (y : ColWords P i T) :
    fixedChildren P hu huM i chosen probes hf (signs P i T x y) =
      decodeRowChildren P hu huM i T chosen (rowChildren P hu huM i T chosen x) y := by
  funext t
  unfold fixedChildren
  rw [N9_native P hu huM t.val.val probes hf hd,children_split P hu huM i T t.val x y]
  rfl

def fixedChildBits : ℕ := ∑ t : ↥chosen, childBits P (rootIndex hu huM t.val.val)

omit [Fintype F] in
theorem fixed_child_tapes_card :
    Fintype.card (RowChildTapes P hu huM i chosen) = 2^fixedChildBits P hu huM i chosen := by
  have h (t : ↥chosen) : Nat.card (ChildTape P (rootIndex hu huM t.val.val)) =
      2^childBits P (rootIndex hu huM t.val.val) :=
    childTape_nat_card P (rootIndex hu huM t.val.val)
  unfold RowChildTapes fixedChildBits
  rw [Fintype.card_pi]
  simp only [← Nat.card_eq_fintype_card,h,Finset.prod_pow_eq_pow_sum]

theorem fixed_child_budget :
    fixedChildBits P hu huM i chosen ≤ chosen.card *
      (64+(12*wireSize V)/(2^rootA V / 2^i.val)) := by
  unfold fixedChildBits
  calc
    _ ≤ ∑ _t : ↥chosen, (64+(12*wireSize V)/(2^rootA V / 2^i.val)) := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [t.val.property] using N9_tape_budget P hu huM t.val.val
    _ = _ := by simp

#print axioms childTape_nat_card
#print axioms childParity_local
#print axioms childParity_switch_local
#print axioms childParity_split
#print axioms children_split
#print axioms N9_fixed_row_native
#print axioms fixed_child_tapes_card
#print axioms fixed_child_budget

end Five
end
end V8NativeMessage