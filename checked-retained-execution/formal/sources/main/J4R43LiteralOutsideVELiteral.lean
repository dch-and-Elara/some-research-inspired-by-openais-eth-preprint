import J4R43LiteralOutsideVariableElim
import J4R43LiteralOutsideEnumeration

/-! The induced-width option starts from the genuine J4 factor graph:
each variable is an actual matched physical column port, and each
factor is the exact old vertex marginal at the printed precision. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R10RowAffine
open J5R41LiteralChildCost
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7300000
set_option maxRecDepth 2300
set_option Elab.async false

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)

local notation "D" => Boundary P i g t
local notation "U" => RowVertex P i g
local notation "V" => ColVertex P i g

def actualRowScope (u : U) : Finset D :=
  Finset.univ.filter (fun m=>∃ q : RowPort P i g u,matchingLink P i g t u q=some m)

def actualColScope (v : V) : Finset D :=
  Finset.univ.filter (fun m=>(boundaryPort P i g t m).1=v)

variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)

def rowMarginal (u : U) (w : D→Bool) : Residue f ell p :=
  ∑ y : RowPort P i g u→Bool,rowTable P i g p old hf u y *
    ∏ q,JointContraction.literal (y q) (JointContraction.wiredInput
      (centreUnit (a:=a) t p hnil) w (matchingLink P i g t u q))

def colMarginal (v : V) (w : D→Bool) : Residue f ell p :=
  ∑ x : ColPort P i g v→Bool,
    if JointContraction.agrees (boundaryPort P i g t) w v x then colTable P i g p old hf v x else 0

theorem actual_row_scope_local (u : U) (x y : D→Bool)
    (same : ∀ m∈actualRowScope P i g t u,x m=y m) :
    rowMarginal P i g t p hnil old hf u x=rowMarginal P i g t p hnil old hf u y := by
  unfold rowMarginal
  refine Finset.sum_congr rfl fun Y _=> ?_
  congr 1
  refine Finset.prod_congr rfl fun q _=> ?_
  cases h : matchingLink P i g t u q with
  | none => rfl
  | some m =>
    have hm : m∈actualRowScope P i g t u := Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,h⟩
    simp only [JointContraction.wiredInput,same m hm]

theorem actual_col_scope_local (v : V) (x y : D→Bool)
    (same : ∀ m∈actualColScope P i g t v,x m=y m) :
    colMarginal P i g t p old hf v x=colMarginal P i g t p old hf v y := by
  unfold colMarginal
  refine Finset.sum_congr rfl fun X _=> ?_
  have eq : JointContraction.agrees (boundaryPort P i g t) x v X ↔
      JointContraction.agrees (boundaryPort P i g t) y v X := by
    constructor
    · intro agree q m link
      have hm : m∈actualColScope P i g t v := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,congrArg Sigma.fst link⟩
      exact (agree q m link).trans (same m hm)
    · intro agree q m link
      have hm : m∈actualColScope P i g t v := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,congrArg Sigma.fst link⟩
      exact (agree q m link).trans (same m hm).symm
  by_cases H : JointContraction.agrees (boundaryPort P i g t) x v X
  · simp only [if_pos H,if_pos (eq.mp H)]
  · simp only [if_neg H,if_neg (fun h=>H (eq.mpr h))]

def literalVEFactors : List (VE.Factor D (Residue f ell p)) :=
  ((Finset.univ : Finset U).toList.map (fun u=>
    VE.fromScope (actualRowScope P i g t u) (rowMarginal P i g t p hnil old hf u)))++
  ((Finset.univ : Finset V).toList.map (fun v=>
    VE.fromScope (actualColScope P i g t v) (colMarginal P i g t p old hf v)))

theorem literal_factors_are_original (w : D→Bool) :
    VE.prodAt (literalVEFactors P i g t p hnil old hf) w =
      JointContraction.rowValue (matchingLink P i g t) (centreUnit (a:=a) t p hnil)
          (rowTable P i g p old hf) w *
        ∏ v : V,colMarginal P i g t p old hf v w := by
  let A (u : U) : VE.Factor D (Residue f ell p) :=
    VE.fromScope (actualRowScope P i g t u) (rowMarginal P i g t p hnil old hf u)
  let B (v : V) : VE.Factor D (Residue f ell p) :=
    VE.fromScope (actualColScope P i g t v) (colMarginal P i g t p old hf v)
  have R :
      (∏ u : U,(A u).eval w) =
        JointContraction.rowValue (matchingLink P i g t) (centreUnit (a:=a) t p hnil)
          (rowTable P i g p old hf) w := by
    unfold JointContraction.rowValue
    refine Finset.prod_congr (Finset.ext fun _=>by simp) fun u _=>?_
    refine (VE.fromScope_exact _ _ (actual_row_scope_local P i g t p hnil old hf u) w).trans ?_
    unfold rowMarginal
    refine Finset.sum_congr (Finset.ext fun _=>by simp) fun y _=>?_
    congr 1
  have C : (∏ v : V,(B v).eval w)=(∏ v : V,colMarginal P i g t p old hf v w) := by
    refine Finset.prod_congr rfl fun v _=>?_
    exact VE.fromScope_exact _ _ (actual_col_scope_local P i g t p old hf v) w
  calc
    _ = (∏ u : U,(A u).eval w)*(∏ v : V,(B v).eval w) := by
      unfold literalVEFactors VE.prodAt
      rw [List.map_append,List.prod_append,List.map_map,List.map_map,Finset.prod_map_toList,
        Finset.prod_map_toList]
      rfl
    _ = _ := congrArg₂ (·*·) R C

theorem literal_factors_boundary_exact :
    VE.activeSum (Finset.univ : Finset D) (literalVEFactors P i g t p hnil old hf) =
      groupBoundaryValue P i g t p hnil old hf := by
  let e : (D→Bool) ≃ (↥(Finset.univ : Finset D)→Bool) :=
    { toFun := fun w d=>w d.val
      invFun := fun w d=>w ⟨d,Finset.mem_univ _⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  let Left : (↥(Finset.univ : Finset D)→Bool)→Residue f ell p := fun y=>
    VE.prodAt (literalVEFactors P i g t p hnil old hf) (VE.extend Finset.univ y)
  let Right : (D→Bool)→Residue f ell p := fun y=>
    JointContraction.rowValue (matchingLink P i g t) (centreUnit (a:=a) t p hnil)
      (rowTable P i g p old hf) y * ∏ b : V,colMarginal P i g t p old hf b y
  change (∑ y,Left y)=_
  calc
    _ = ∑ y,Right y := by
      apply Fintype.sum_equiv e.symm Left Right
      intro y
      dsimp only [Left,Right]
      have yy : VE.extend (Finset.univ : Finset D) y=e.symm y := by
        funext q
        simp [VE.extend,e]
      rw [yy,literal_factors_are_original]
    _ = _ := by
      unfold groupBoundaryValue
      refine Finset.sum_congr (Finset.ext fun _=>by simp) fun y _=>?_
      rfl

#print axioms actual_row_scope_local
#print axioms actual_col_scope_local
#print axioms literal_factors_are_original
#print axioms literal_factors_boundary_exact
end
end J4R43LiteralOutside

