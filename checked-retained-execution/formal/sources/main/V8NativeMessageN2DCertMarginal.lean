import J6R10RepackRounded
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 21000000

/-! Project the full *real* declared cell counts (not padded seats)
onto a specified side and label of the actual half-port child. -/
namespace V8NativeMessage.N2DCert
open Real J6R10Repack P11FullPacking
open scoped Classical BigOperators

noncomputable section

variable {E : Type*} {a : ℕ}

abbrev Cells (a : ℕ) := Cell (Fin a) (Fin 64)

abbrev SideCells (i : Fin a) (right : Bool) (g : Fin 64) :=
  {c : Cells a // atEnd i right c=g}

abbrev SideEdges (label : E→Cells a) (i : Fin a) (right : Bool) (g : Fin 64) :=
  {e : E // atEnd i right (label e)=g}

def side_fibre_equiv (label : E→Cells a) (i : Fin a) (right : Bool) (g : Fin 64) :
    SideEdges label i right g ≃ Σ c : SideCells i right g,Fiber label c.val where
  toFun e := ⟨⟨label e.val,e.property⟩,⟨e.val,rfl⟩⟩
  invFun t := ⟨t.2.val,by rw [t.2.property]; exact t.1.property⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨c,hc⟩,⟨e,he⟩⟩
    change label e=c at he
    subst c
    rfl

variable [Fintype E]

theorem side_card_sum (label : E→Cells a) (i : Fin a) (right : Bool) (g : Fin 64) :
    (Nat.card (SideEdges label i right g):ℝ) =
      ∑ c : SideCells i right g,(Nat.card (Fiber label c.val):ℝ) := by
  letI (c : SideCells i right g) : Fintype (Fiber label c.val) := Fintype.ofFinite _
  have h := Nat.card_congr (side_fibre_equiv label i right g)
  calc
    _ = (Nat.card (Σ c : SideCells i right g,Fiber label c.val):ℝ) :=
      congrArg (fun x : ℕ=>(x:ℝ)) h
    _ = _ := by
      rw [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Nat.card_eq_fintype_card]

omit [Fintype E] in
theorem one_cell_margin (label : E→Cells a) (Δ : ℕ)
    (hΦ : varianceScore label≤2*(Nat.card E:ℚ)*Δ) (c : Cells a) :
    let μ := (Nat.card E:ℝ)/(Nat.card (Cells a):ℝ)
    let e := sqrt (2*(Nat.card E:ℝ)*(Δ:ℝ))
    μ-e≤(Nat.card (Fiber label c):ℝ) ∧
      (Nat.card (Fiber label c):ℝ)≤μ+e := by
  let μ : ℝ := (Nat.card E:ℝ)/(Nat.card (Cells a):ℝ)
  let e : ℝ := sqrt (2*(Nat.card E:ℝ)*(Δ:ℝ))
  have hq : ((Nat.card (Fiber label c):ℚ)-(Nat.card E:ℚ)/Nat.card (Cells a))^2
      ≤2*(Nat.card E:ℚ)*Δ :=
    (Finset.single_le_sum
      (f:=fun k : Cells a=>((Nat.card (Fiber label k):ℚ)-(Nat.card E:ℚ)/Nat.card (Cells a))^2)
      (fun _ _=>sq_nonneg _) (Finset.mem_univ c)).trans hΦ
  have hR : ((Nat.card (Fiber label c):ℝ)-μ)^2≤2*(Nat.card E:ℝ)*(Δ:ℝ) := by
    unfold μ
    have hcast := (Rat.cast_le (K:=ℝ)).2 hq
    push_cast at hcast
    exact hcast
  have he : 0≤e := sqrt_nonneg _
  have ha : |(Nat.card (Fiber label c):ℝ)-μ|≤e := by
    apply (sq_le_sq₀ (abs_nonneg _) he).mp
    rw [sq_abs]
    unfold e
    rw [sq_sqrt (by positivity)]
    exact hR
  obtain ⟨hl,hu⟩ := abs_le.mp ha
  change μ-e≤(Nat.card (Fiber label c):ℝ) ∧
    (Nat.card (Fiber label c):ℝ)≤μ+e
  exact ⟨by linarith only [hl],by linarith only [hu]⟩

theorem cell_card_positive (a : ℕ) : 0 < Nat.card (Cells a) := by
  rw [total_cells,Fintype.card_fin]
  positivity

theorem side_margin (label : E→Cells a) (Δ : ℕ)
    (hΦ : varianceScore label≤2*(Nat.card E:ℚ)*Δ)
    (i : Fin a) (right : Bool) (g : Fin 64) :
    let M := (Nat.card E:ℝ)
    let e := (Nat.card (Cells a):ℝ)*sqrt (2*M*(Δ:ℝ))
    M-e≤64*(Nat.card (SideEdges label i right g):ℝ) ∧
      64*(Nat.card (SideEdges label i right g):ℝ)≤M+e := by
  let M : ℝ := Nat.card E
  let D : ℝ := Nat.card (Cells a)
  let E₀ : ℝ := sqrt (2*M*(Δ:ℝ))
  let k : ℝ := Fintype.card (SideCells i right g)
  let n : ℝ := Nat.card (SideEdges label i right g)
  have hD : 0 < D := by
    change (0:ℝ)<Nat.card (Cells a)
    exact_mod_cast cell_card_positive a
  have hk : 64*k=D := by
    have h := side_cell_card i right g
    rw [Fintype.card_fin,Nat.card_eq_fintype_card (α:=SideCells i right g)] at h
    change (64:ℝ)*(Fintype.card (SideCells i right g):ℝ)=
      (Nat.card (Cells a):ℝ)
    exact_mod_cast h
  have hbase : 64*(k*(M/D))=M := by
    calc
      _ = (64*k)*(M/D) := by ring
      _ = (M/D)*D := by rw [hk,mul_comm]
      _ = _ := div_mul_cancel₀ _ hD.ne'
  have herr : 64*(k*E₀)=D*E₀ := by rw [←hk]; ring
  have hLo : (∑ _c : SideCells i right g,(M/D-E₀))≤
      ∑ c : SideCells i right g,(Nat.card (Fiber label c.val):ℝ) := by
    refine Finset.sum_le_sum (s := Finset.univ) ?_
    intro c _
    exact (one_cell_margin label Δ hΦ c.val).1
  have hUp : (∑ c : SideCells i right g,(Nat.card (Fiber label c.val):ℝ))≤
      ∑ _c : SideCells i right g,(M/D+E₀) := by
    refine Finset.sum_le_sum (s := Finset.univ) ?_
    intro c _
    exact (one_cell_margin label Δ hΦ c.val).2
  rw [←side_card_sum label i right g] at hLo hUp
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hLo hUp
  change k*(M/D-E₀)≤n at hLo
  change n≤k*(M/D+E₀) at hUp
  have hl := mul_le_mul_of_nonneg_left hLo (by norm_num : (0:ℝ)≤64)
  have hu := mul_le_mul_of_nonneg_left hUp (by norm_num : (0:ℝ)≤64)
  change M-D*E₀≤64*n ∧ 64*n≤M+D*E₀
  constructor <;> nlinarith only [hl,hu,hbase,herr]

variable {A B : Type*}

theorem exact_child_margin (N : Network E A B) (P : PhysicalPacking N a (Fin 64))
    (Δ : ℕ) (hΦ : varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(Nat.card E:ℚ)*Δ)
    (i : Fin a) (g : Fin 64) :
    let M := (Nat.card E:ℝ)
    let e := (Nat.card (Cells a):ℝ)*sqrt (2*M*(Δ:ℝ))
    let m := (Nat.card (ChildEdge N (declaredGroup P.rowLabel P.colLabel i) g):ℝ)
    M-e≤32*m ∧ 32*m≤M+e := by
  let label := declaredCell N P.rowLabel P.colLabel
  let gr := declaredGroup P.rowLabel P.colLabel i
  let M : ℝ := Nat.card E
  let e : ℝ := (Nat.card (Cells a):ℝ)*sqrt (2*M*(Δ:ℝ))
  let b₀ : ℝ := Nat.card (rowsIn N gr g)
  let b₁ : ℝ := Nat.card (colsIn N gr g)
  let m : ℝ := Nat.card (ChildEdge N gr g)
  have h0 : M-e≤64*b₀ ∧ 64*b₀≤M+e := side_margin label Δ hΦ i false g
  have h1 : M-e≤64*b₁ ∧ 64*b₁≤M+e := side_margin label Δ hΦ i true g
  have hm : m=b₀+b₁ := by
    change (Nat.card (ChildEdge N gr g):ℝ)=
      (Nat.card (rowsIn N gr g):ℝ)+(Nat.card (colsIn N gr g):ℝ)
    exact_mod_cast child_edges_exact N gr g
  change M-e≤32*m ∧ 32*m≤M+e
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,hm]

#print axioms side_fibre_equiv
#print axioms side_card_sum
#print axioms one_cell_margin
#print axioms cell_card_positive
#print axioms side_margin
#print axioms exact_child_margin
end
end V8NativeMessage.N2DCert
