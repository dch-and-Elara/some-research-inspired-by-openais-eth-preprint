import P5AlwaysSatOriginalPhysicalFibre
import P5HybridClosureDPack
import P5HybridClosureDensity
import J1MainSourceBridge
import P5MainIteratorSourceLayout

/-! Plain MAIN labels and source seats for finite, actual incidence charts.
In particular (M.7) needs no planted ties. Its distinct real-copy and
factor keys have the independent source law before balancing. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
open J1MainSourceLabels J1MainSourceCollision J1MainSourceBridge J1MainSourcePlacement
open DiagonalAbundance
open P5MainIterator
open Paper5.HybridClosure (bad_pairs_with_ties mean_le_select deviation_load_bound)

section Untied
variable {P W F I S : Type*} [Fintype P] [Fintype W] [Fintype F]
  [Nonempty P] [Nonempty W] [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
variable (special : I) (own : P→W) (fac : P→F)

abbrev WeightKeys (W F I : Type*) := Primitive W F Unit I

def noTie : F→Option Unit := fun _=>none

noncomputable def mainData (cfg : WeightKeys W F I→S) : IncidenceData I S P W F :=
  originalData special noTie own fac cfg

omit [Fintype P] [Fintype W] [Fintype F] [Nonempty P] [Nonempty W] [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] in
theorem untied_factor_key (f : F) (i : I) :
    factorKey special (noTie (F:=F)) f i = .inl (f,i) := by
  by_cases h : i=special <;> simp [factorKey,noTie,h]

set_option maxHeartbeats 3500000 in
/-- The score choice charges both variable-group load and ordered cell
load. The bound uses the literal incidence lemma's b+w, and no assumed
physical layout. -/
theorem actual_MAIN_labels (b w : ℕ) (hbw : 0<b+w)
    (hv : ∀ v : W, Nat.card {e : P // own e=v}≤b)
    (hf : ∀ f : F, Nat.card {e : P // fac e=f}≤w)
    (hcell : 2*((b+w:ℕ):ℚ)*(Fintype.card (Draw I S):ℚ)^2≤Fintype.card P)
    (hgrp : 2*(Fintype.card I:ℚ)*(Fintype.card S:ℚ)^2≤Fintype.card W) :
    ∃ cfg : WeightKeys W F I→S,
      (∀ u, load (mainData special own fac cfg).cell u≤
        2*(Fintype.card P:ℚ)/(Fintype.card (Draw I S):ℚ)) ∧
      ∀ i g,load (fun v : W=>(mainData special own fac cfg).wordVar v i) g≤
        2*(Fintype.card W:ℚ)/(Fintype.card S:ℚ) := by
  classical
  let M : ℚ := Fintype.card P
  let n : ℚ := Fintype.card W
  let Q : ℚ := Fintype.card I
  let C : ℚ := (b+w:ℕ)
  let Φ := incidenceCost (S:=S) special (noTie (F:=F)) own fac
  let Ξ := variableCost (V:=W) (F:=F) (B:=Unit) (I:=I) (S:=S)
  have hM : 0<M := by dsimp [M]; exact_mod_cast Fintype.card_pos (α:=P)
  have hn : 0<n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α:=W)
  have hQ : 0<Q := by dsimp [Q]; exact_mod_cast Fintype.card_pos (α:=I)
  have hC : 0<C := by dsimp [C]; exact_mod_cast hbw
  have hbad := bad_pairs_with_ties (noTie (F:=F)) own fac b w 0 0
    (fun v=>by
      change (J6R11Collision.fibre own v).card≤_
      rw [J6R11CollisionReindex.card_filter_fibre]
      exact hv v)
    (fun f=>by
      change (J6R11Collision.fibre fac f).card≤_
      rw [J6R11CollisionReindex.card_filter_fibre]
      exact hf f)
    (by intro u; cases u; simp [noTie,tagFibre])
    (by simp [tiedSlots,noTie])
  have hΦ : mean Φ≤M*C := by
    refine (expected_incidenceCost (S:=S) special noTie own fac).trans ?_
    have hbound : (badPairs (noTie (F:=F)) own fac).card≤(b+w)*Fintype.card P :=
      hbad.trans (by
        rw [zero_mul,add_zero]
        exact Nat.mul_le_mul_right _ (by omega))
    have h : ((badPairs (noTie (F:=F)) own fac).card:ℚ)≤((b+w:ℕ):ℚ)*(Fintype.card P:ℚ) := by
      exact_mod_cast hbound
    simpa only [M,C,mul_comm] using h
  have hΞ : mean Ξ≤Q*n := expected_variableCost
  let score := fun cfg=>(M*C)⁻¹*Φ cfg+(Q*n)⁻¹*Ξ cfg
  have hx : mean score≤2 := by
    unfold score
    rw [mean_lin_add,mean_scale,mean_scale,inv_mul_eq_div,inv_mul_eq_div]
    have h₁ : mean Φ/(M*C)≤1 := (div_le_iff₀ (mul_pos hM hC)).mpr (by simpa using hΦ)
    have h₂ : mean Ξ/(Q*n)≤1 := (div_le_iff₀ (mul_pos hQ hn)).mpr (by simpa using hΞ)
    linarith only [h₁,h₂]
  obtain ⟨cfg,hcfg⟩ := mean_le_select score
  have h₂ := hcfg.trans hx
  have hφ0 : 0≤Φ cfg := deviation_nonneg _
  have hξ0 : 0≤Ξ cfg := Finset.sum_nonneg (fun _ _=>deviation_nonneg _)
  have hφ : Φ cfg≤2*M*C := by
    have hr : (M*C)⁻¹*Φ cfg≤2 := by
      exact (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (mul_pos hQ hn).le) hξ0)).trans h₂
    rw [inv_mul_eq_div,div_le_iff₀ (mul_pos hM hC)] at hr
    linarith only [hr]
  have hξ : Ξ cfg≤2*n*Q := by
    have hr : (Q*n)⁻¹*Ξ cfg≤2 := by
      exact (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr (mul_pos hM hC).le) hφ0)).trans h₂
    rw [inv_mul_eq_div,div_le_iff₀ (mul_pos hQ hn)] at hr
    linarith only [hr]
  refine ⟨cfg,fun u=>?_,fun i g=>?_⟩
  · exact deviation_load_bound _ C hφ hcell u
  · have hs := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun i=> deviation (fun v : W=> variableWord cfg v i))
      (fun _ _=>deviation_nonneg _) (Finset.mem_univ i)
    exact deviation_load_bound _ Q (hs.trans hξ) hgrp g
end Untied

def mainCellEquiv (I S : Type*) : Draw I S ≃ WordCell I S where
  toFun p := fun i=>(p.1 i,p.2 i)
  invFun c := (fun i=>(c i).1,fun i=>(c i).2)
  left_inv p := by cases p; rfl
  right_inv p := by funext i; exact Prod.ext rfl rfl

section Seating
variable {P W F I S : Type*} [Fintype P] [Fintype I] [Fintype S] [LinearOrder S]
variable (D : IncidenceData I S P W F) (surj : Function.Surjective D.var)

noncomputable def MAINlayout :
    SourceLayout P W F (Fin (copies D)) I S where
  placement :=
    { owner := D.var
      occurs := surj
      slot :=
        ⟨fun e=>(copyIndex D (copies D) (copies_suffice D) e,
            mainCellEquiv I S (D.cell e)),
         by
           intro e f h
           apply position_injective D (copies D) (copies_suffice D)
           have h₁ := congrArg (fun x : Fin (copies D)×WordCell I S=>x.1) h
           have h₂ := congrArg (fun x : Fin (copies D)×WordCell I S=>x.2) h
           exact Prod.ext h₁ ((mainCellEquiv I S).injective h₂)⟩ }
  factor := D.factor
  a := D.wordVar
  d := D.wordFactor
  first _ _ := rfl
  second _ _ := rfl

theorem MAIN_layout_reads (e : P) :
    occupied D (copies D) (copies_suffice D)
      (((MAINlayout D surj).placement.slot e).1) (D.cell e)=some (D.var e) :=
  occupied_at D _ _ e

omit [LinearOrder S] in
theorem MAIN_exact_copies [Nonempty S] (cap : ℚ) (hcap : ∀ c : Draw I S,load D.cell c≤cap) :
    (copies D:ℚ)≤cap := by
  let n := fun c : Draw I S=>Fintype.card (CellFibre D c)
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image Finset.univ n Finset.univ_nonempty
  have h : copies D≤n u := copies_budget D _ (fun c=>hu c (Finset.mem_univ _))
  have hh : (n u:ℚ)=load D.cell u := by
    unfold n
    rw [←Nat.card_eq_fintype_card]
    exact J6R11CollisionReindex.card_fibre_load D.cell u
  exact (show (copies D:ℚ)≤n u by exact_mod_cast h).trans (hh ▸ hcap u)
end Seating

#print axioms untied_factor_key
#print axioms actual_MAIN_labels
#print axioms MAINlayout
#print axioms MAIN_layout_reads
#print axioms MAIN_exact_copies
end Paper5.AlwaysSatOriginal.Physical