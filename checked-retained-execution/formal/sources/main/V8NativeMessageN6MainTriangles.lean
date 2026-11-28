import P5HybridClosureTriangle
import V8CapacityUnifiedMatching

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

/-! The original target is the product over the three actual edges
of each triangle in the v7 replacement graph. All nonselected pins
are set to true. The chart changes no exterior edge or source factor. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators
open Paper5.HybridClosure V8CapacityUnified.U7
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleValue (v : V) (σ : TriVertex V→Bool) : ℚ :=
  ∏ j : Fin 3, pairOR ℚ (σ (v,j)) (σ (v,j+1))

def UM (σ : TriVertex V→Bool) : ℚ := ∏ v, triangleValue v σ

theorem UM_is_inner_edges (σ : TriVertex V→Bool) :
    UM σ = ∏ e ∈ innerEdges V, pairOR ℚ (σ e.1) (σ e.2) := by
  unfold UM triangleValue innerEdges
  rw [Finset.prod_image (fun _ _ _ _ h => innerEdge_injective h)]
  exact (Fintype.prod_prod_type (fun u : V × Fin 3 =>
    pairOR ℚ (σ (innerEdge u).1) (σ (innerEdge u).2))).symm

omit [Fintype V] [DecidableEq V] in
theorem one_triangle (l r : Fin 3) (hd : l≠r) (x y : Bool) :
    (∏ j : Fin 3,
      pairOR ℚ (if j=l then x else if j=r then y else true)
        (if j+1=l then x else if j+1=r then y else true)) = pairOR ℚ x y := by
  rw [Fin.prod_univ_three]
  change pairOR ℚ (if (0 : Fin 3)=l then x else if (0 : Fin 3)=r then y else true)
      (if (1 : Fin 3)=l then x else if (1 : Fin 3)=r then y else true) *
    pairOR ℚ (if (1 : Fin 3)=l then x else if (1 : Fin 3)=r then y else true)
      (if (2 : Fin 3)=l then x else if (2 : Fin 3)=r then y else true) *
    pairOR ℚ (if (2 : Fin 3)=l then x else if (2 : Fin 3)=r then y else true)
      (if (0 : Fin 3)=l then x else if (0 : Fin 3)=r then y else true) = _
  fin_cases l <;> fin_cases r <;>
    first | exact (hd rfl).elim | (cases x <;> cases y <;> norm_num [pairOR,Fin.ext_iff])

structure TriangleSlice (V : Type*) (m : ℕ) where
  vertex : Fin m ↪ V
  left : Fin m → Fin 3
  right : Fin m → Fin 3
  distinct : ∀ j, left j≠right j

variable {m : ℕ} (S : TriangleSlice V m)

def leftPin (i : Fin m) : TriVertex V := (S.vertex i,S.left i)
def rightPin (i : Fin m) : TriVertex V := (S.vertex i,S.right i)

def word (x y : Fin m→Bool) (p : TriVertex V) : Bool :=
  if hv : p.1 ∈ Set.range S.vertex then
    let i := Classical.choose hv
    if p.2=S.left i then x i else if p.2=S.right i then y i else true
  else true

omit [Fintype V] in
theorem word_at_vertex (x y : Fin m→Bool) (i : Fin m) (j : Fin 3) :
    word S x y (S.vertex i,j) =
      if j=S.left i then x i else if j=S.right i then y i else true := by
  let hv : S.vertex i ∈ Set.range S.vertex := ⟨i,rfl⟩
  unfold word
  rw [dif_pos hv]
  have hw : Classical.choose hv=i := S.vertex.injective (Classical.choose_spec hv)
  rw [hw]

omit [Fintype V] in
theorem word_off_pairs (x y : Fin m→Bool) (p : TriVertex V)
    (hl : ∀ i, p≠leftPin S i) (hr : ∀ i, p≠rightPin S i) :
    word S x y p=true := by
  by_cases hh : p.1 ∈ Set.range S.vertex
  · let i := Classical.choose hh
    have hi : S.vertex i = p.1 := Classical.choose_spec hh
    have el : p.2 ≠ S.left i := fun he => hl i (Prod.ext hi.symm he)
    have er : p.2 ≠ S.right i := fun he => hr i (Prod.ext hi.symm he)
    simp [word,hh,show p.2≠S.left (Classical.choose hh) from el,
      show p.2≠S.right (Classical.choose hh) from er]
  · simp only [word,dif_neg hh]

omit [Fintype V] in
theorem word_cross_left (x y : Fin m→Bool) (cut : TriVertex V→Bool)
    (hr : ∀ i, cut (rightPin S i)=false) (p : TriVertex V) (hp : cut p=true) :
    word S x y p=word S x (fun _ => true) p := by
  by_cases hh : p.1 ∈ Set.range S.vertex
  · let i := Classical.choose hh
    have hi : S.vertex i = p.1 := Classical.choose_spec hh
    have er : p.2 ≠ S.right i := by
      intro he
      have ep : p=rightPin S i := Prod.ext hi.symm he
      cases (hp.symm.trans (ep ▸ hr i))
    simp [word,hh,show p.2≠S.right (Classical.choose hh) from er]
  · simp only [word,dif_neg hh]

omit [Fintype V] in
theorem word_cross_right (x y : Fin m→Bool) (cut : TriVertex V→Bool)
    (hl : ∀ i, cut (leftPin S i)=true) (p : TriVertex V) (hp : cut p=false) :
    word S x y p=word S (fun _ => true) y p := by
  by_cases hh : p.1 ∈ Set.range S.vertex
  · let i := Classical.choose hh
    have hi : S.vertex i = p.1 := Classical.choose_spec hh
    have el : p.2 ≠ S.left i := by
      intro he
      have ep : p=leftPin S i := Prod.ext hi.symm he
      cases (hp.symm.trans (ep ▸ hl i))
    simp [word,hh,show p.2≠S.left (Classical.choose hh) from el]
  · simp only [word,dif_neg hh]

theorem UM_on_slice (x y : Fin m→Bool) :
    UM (word S x y) = matchingTarget ℚ m x y := by
  let A : Finset V := (Finset.univ : Finset (Fin m)).map S.vertex
  unfold UM matchingTarget
  rw [Matrix.of_apply]
  have gone : ∀ v ∈ (Finset.univ : Finset V), v∉A → triangleValue v (word S x y)=1 := by
    intro v _ hv
    have hh : v∉Set.range S.vertex := by
      rintro ⟨i,hi⟩
      exact hv (Finset.mem_map.mpr ⟨i,Finset.mem_univ i,hi⟩)
    simp [triangleValue,word,hh,pairOR]
  calc
    _ = ∏ v∈A, triangleValue v (word S x y) :=
      (Finset.prod_subset (Finset.subset_univ A) gone).symm
    _ = ∏ i : Fin m, triangleValue (S.vertex i) (word S x y) := Finset.prod_map _ _ _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [triangleValue,word_at_vertex] using one_triangle (S.left i) (S.right i) (S.distinct i) (x i) (y i)

def wholeTriangles {G : Type*} [DecidableEq G] (owner : TriVertex V→G) (g : G) : Finset V :=
  Finset.univ.filter (fun v => ∀ j, owner (v,j)=g)

def groupSlice {G : Type*} [DecidableEq G] (owner : TriVertex V→G) (g : G) :
    TriangleSlice V (wholeTriangles owner g).card where
  vertex := ((Fintype.equivFinOfCardEq (Fintype.card_coe (wholeTriangles owner g))).symm.toEmbedding).trans
    ⟨Subtype.val,Subtype.val_injective⟩
  left _ := 0
  right _ := 1
  distinct _ := by decide

omit [DecidableEq V] in
theorem groupSlice_seated {G : Type*} [DecidableEq G] (owner : TriVertex V→G) (g : G)
    (i : Fin (wholeTriangles owner g).card) (j : Fin 3) :
    owner ((groupSlice owner g).vertex i,j)=g := by
  let v := (Fintype.equivFinOfCardEq (Fintype.card_coe (wholeTriangles owner g))).symm i
  exact (Finset.mem_filter.mp v.property).2 j

#print axioms UM_is_inner_edges
#print axioms one_triangle
#print axioms word_at_vertex
#print axioms word_off_pairs
#print axioms word_cross_left
#print axioms word_cross_right
#print axioms UM_on_slice
#print axioms groupSlice_seated

end
end V8NativeMessage.N6
