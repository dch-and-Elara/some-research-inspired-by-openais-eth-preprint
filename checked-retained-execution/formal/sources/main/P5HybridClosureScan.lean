import P5HybridClosureProduct

/-! §8 exact indexed-word scan cost. The public preprocessing supplies each
bucket's list once. At each edge there are two sign reads, one OR, and one
Boolean product. Each bucket and the final merge consume one multiplication. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def scanEdgeList {T : Type*} (x : T→Bool) : List (T×T)→Bool×ℕ
  | [] => (true,0)
  | (u,v)::es =>
    let recOut := scanEdgeList x es
    ((x u || x v) && recOut.1, 4+recOut.2)

def boolAsNat (b : Bool) : ℕ := if b then 1 else 0

theorem boolAsNat_or_and (a b c : Bool) :
    boolAsNat ((a || b) && c) = boolOrNat a b * boolAsNat c := by
  cases a <;> cases b <;> cases c <;> decide

theorem scanEdgeList_exact {T : Type*} (x : T→Bool) (xs : List (T×T)) :
    boolAsNat (scanEdgeList x xs).1 = (xs.map (edgeOr x)).prod ∧
      (scanEdgeList x xs).2 = 4*xs.length := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
    obtain ⟨u,v⟩ := e
    constructor
    · simp only [scanEdgeList,boolAsNat_or_and,ih.1,List.map_cons,List.prod_cons,edgeOr]
    · simp only [scanEdgeList,ih.2,List.length_cons]
      omega

section Local
variable {W C : Type*} [DecidableEq C]

/-- The two addresses of every retained edge inhabit *this* group, not a
superset of global input pins. Construct the typed index list before reading
any signs. -/
noncomputable def preindexed (F : Finset (W×W)) (c : W→C)
    (mono : ∀e∈F,c e.1=c e.2) (g : C) :
    List ({w : W // c w=g}×{w : W // c w=g}) :=
  (bucketEdges F c g).attach.toList.map fun (e : ↥(bucketEdges F c g)) =>
    let h : e.val∈F.filter (fun p => c p.1=g) := e.property
    (⟨e.val.1,(Finset.mem_filter.mp h).2⟩,
     ⟨e.val.2,(mono e.val (Finset.mem_filter.mp h).1).symm.trans
       (Finset.mem_filter.mp h).2⟩)

theorem preindexed_length (F : Finset (W×W)) (c : W→C) (mono : ∀e∈F,c e.1=c e.2)
    (g : C) : (preindexed F c mono g).length=(bucketEdges F c g).card := by
  simp [preindexed]

theorem scan_group_exact (F : Finset (W×W)) (c : W→C) (mono : ∀e∈F,c e.1=c e.2)
    (g : C) (x : SignGroup c g) :
    boolAsNat (scanEdgeList x (preindexed F c mono g)).1 = groupOperand F c mono g x ∧
      (scanEdgeList x (preindexed F c mono g)).2 = 4*(bucketEdges F c g).card := by
  obtain ⟨hv,hc⟩ := scanEdgeList_exact x (preindexed F c mono g)
  constructor
  · rw [hv]
    unfold groupOperand preindexed
    rw [List.map_map,Finset.prod_map_toList]
    rfl
  · rw [hc,preindexed_length]
end Local

section Full
variable {W C : Type*} [Fintype C] [DecidableEq C]

def completeScans {D : Type*} (f : D→Bool×ℕ) : List D→Bool×ℕ
  | [] => (true,0)
  | g::gs =>
    let a := f g
    let b := completeScans f gs
    (a.1 && b.1, a.2 + b.2 + 1)

theorem completeScans_exact {D : Type*} (f : D→Bool×ℕ) (gs : List D) :
    boolAsNat (completeScans f gs).1=(gs.map (fun g => boolAsNat (f g).1)).prod ∧
      (completeScans f gs).2=(gs.map (fun g => (f g).2)).sum+gs.length := by
  have hmul : ∀ a b, boolAsNat (a && b)=boolAsNat a * boolAsNat b := by decide
  induction gs with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih =>
    constructor
    · simp only [completeScans,hmul,ih.1,List.map_cons,List.prod_cons]
    · simp only [completeScans,ih.2,List.map_cons,List.sum_cons,List.length_cons]
      omega

noncomputable def completeFamily (F : Finset (W×W)) (c : W→C) (mono : ∀e∈F,c e.1=c e.2)
    (σ : W→Bool) : Bool×ℕ :=
  completeScans (fun g => scanEdgeList (σ ∘ Subtype.val) (preindexed F c mono g))
    (Finset.univ : Finset C).toList

theorem completeFamily_exact (F : Finset (W×W)) (c : W→C) (mono : ∀e∈F,c e.1=c e.2)
    (σ : W→Bool) :
    boolAsNat (completeFamily F c mono σ).1 = ∏ e∈F,edgeOr σ e ∧
      (completeFamily F c mono σ).2 = 4*F.card + Fintype.card C := by
  obtain ⟨hv,hc⟩ := completeScans_exact
    (fun g => scanEdgeList (σ ∘ Subtype.val) (preindexed F c mono g))
    (Finset.univ : Finset C).toList
  have hs (g : C) := scan_group_exact F c mono g (σ ∘ Subtype.val)
  constructor
  · rw [completeFamily,hv,Finset.prod_map_toList]
    simp_rw [(hs _).1]
    exact completed_operand F c mono σ
  · rw [completeFamily,hc,Finset.sum_map_toList,Finset.length_toList,Finset.card_univ]
    simp_rw [(hs _).2]
    rw [←Finset.mul_sum,preassigned_bucket_sizes]
end Full

section SourceMerge
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

noncomputable def twoMethodScan (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (cM : V→A) (cD : E→B) (σ : TriVertex V→Bool) : Bool×ℕ :=
  let m := completeFamily (innerEdges V) (mainPinColor cM) (main_inner_monochromatic cM) σ
  let d := completeFamily (outerEdges E cubic) (dPinColor E cubic cD) (d_outer_monochromatic E cubic cD) σ
  (m.1 && d.1,m.2+d.2+1)

theorem twoMethodScan_exact (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
    (loopless : ∀v,(v,v)∉E) (cM : V→A) (cD : E→B)
    (left right : (replacedEdges E cubic)→Fin 4) (σ : TriVertex V→Bool) :
    boolAsNat (twoMethodScan E cubic cM cD σ).1 =
      PinnedCNF.modelCount (MainClonedCNF.formula (replacedEdges E cubic) left right σ) ∧
    (twoMethodScan E cubic cM cD σ).2 =
      6*Fintype.card (TriVertex V)+Fintype.card A+Fintype.card B+1 := by
  have m := completeFamily_exact (innerEdges V) (mainPinColor cM) (main_inner_monochromatic cM) σ
  have d := completeFamily_exact (outerEdges E cubic) (dPinColor E cubic cD) (d_outer_monochromatic E cubic cD) σ
  have hmul : ∀ a b, boolAsNat (a && b)=boolAsNat a * boolAsNat b := by decide
  constructor
  · rw [twoMethodScan,hmul,m.1,d.1,←Finset.prod_union (triangle_split_disjoint E cubic loopless)]
    rw [MainClonedCNF.modelCount_cloned,PinnedCNF.count_eq_indicator]
    exact edge_product_is_indicator (replacedEdges E cubic) σ
  · rw [twoMethodScan,m.2,d.2]
    have h := triangle_edge_count E cubic loopless
    rw [replacedEdges,Finset.card_union_of_disjoint (triangle_split_disjoint E cubic loopless)] at h
    omega
end SourceMerge

#print axioms scanEdgeList_exact
#print axioms scan_group_exact
#print axioms completeScans_exact
#print axioms completeFamily_exact
#print axioms twoMethodScan_exact
end Paper5.HybridClosure