import J4R43LiteralOutsidePhysicalSupply

/-! Explicit actual finite inequalities replacing the manuscript's
asymptotic load comparison. Sufficient population thresholds are
derived from the certified sum of squared load deviations and rounding. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J6R10Repack
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5500000

theorem exact_sum_of_fibers {E C : Type*} [Fintype E] [Fintype C] (label : E→C) :
    (∑ c : C,Nat.card (Fiber label c))=Nat.card E := by
  letI (c : C) : Fintype (Fiber label c) := Fintype.ofFinite _
  have E' := Nat.card_congr (Equiv.sigmaFiberEquiv label)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using E'

variable {E A B G : Type} [Fintype E] [Fintype G] [LinearOrder G] [Nonempty G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G)

abbrev nCells := Nat.card (Cell (Fin a) G)

theorem actual_census_from_variance (d : ℕ)
    (copies : P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)))
    (var : varianceScore (declaredCell N P.rowLabel P.colLabel)≤6*(Nat.card E:ℚ))
    (rough : 384*(nCells (a:=a) (G:=G))^2≤Nat.card E)
    (mesh : 8*2^a*nCells (a:=a) (G:=G)≤Nat.card E)
    (small : 4*starWidth d*nCells (a:=a) (G:=G)≤Nat.card E)
    (large : 64*(reciprocal d)^2*(starWidth d)^2*(nCells (a:=a) (G:=G))^2≤Nat.card E) :
    0<P.copies ∧
      (∀ c : Cell (Fin a) G, fullLoad P+2*starWidth d≤2*Nat.card (InputCell P c)) ∧
      64*(reciprocal d)^2*(starWidth d)^2*Nat.card E≤(fullLoad P)^2 := by
  let L := (2:ℕ)^a
  let M := Nat.card E
  let D := nCells (a:=a) (G:=G)
  let lab := declaredCell N P.rowLabel P.colLabel
  let H := fullLoad P
  let μ : ℚ := M/(D:ℚ)
  let g := maxFiber lab
  have Dn : 0<D := by
    unfold D nCells
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have Dp : (0:ℚ)<D := by exact_mod_cast Dn
  have Mp : 0<M := by
    have h : 0<384*D^2 := by positivity
    exact h.trans_le rough
  have up : 0<μ := by
    dsimp only [μ]
    exact div_pos (by exact_mod_cast Mp) Dp
  have Lp : 0<L := by unfold L; positivity
  have rounds : g≤H ∧ H<g+L := by
    unfold H fullLoad
    rw [copies]
    exact rounded_capacity L g Lp
  have a_sq : 6*(M:ℚ)≤(μ/8)^2 := by
    have h : (384:ℚ)*(D:ℚ)^2≤M := by exact_mod_cast rough
    have K : (0:ℚ)<(8*(D:ℚ))^2 := by positivity
    have q : μ/8=(M:ℚ)/(8*(D:ℚ)) := by dsimp only [μ]; ring
    rw [q,div_pow]
    apply (le_div_iff₀ K).mpr
    calc
      _ = ((384:ℚ)*(D:ℚ)^2)*(M:ℚ) := by ring
      _ ≤ (M:ℚ)*(M:ℚ) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have a_close (c : Cell (Fin a) G) : |(Nat.card (InputCell P c):ℚ)-μ|≤μ/8 := by
    have h : ((Nat.card (InputCell P c):ℚ)-μ)^2≤varianceScore lab := by
      unfold varianceScore
      exact Finset.single_le_sum (fun k _=>sq_nonneg ((Nat.card (Fiber lab k):ℚ)-μ)) (Finset.mem_univ c)
    have q := (h.trans var).trans a_sq
    rw [←sq_abs] at q
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp q
  obtain ⟨c0,hc0⟩ := attained_max lab
  have gh : (g:ℚ)≤μ+μ/8 := by
    have h := (abs_le.mp (a_close c0)).2
    change (Nat.card (Fiber lab c0):ℚ)-μ≤μ/8 at h
    rw [hc0] at h
    linarith
  have Lh : (L:ℚ)≤μ/8 := by
    have h : (8:ℚ)*(L:ℚ)*(D:ℚ)≤M := by exact_mod_cast mesh
    have q : μ/8=(M:ℚ)/(8*(D:ℚ)) := by dsimp only [μ]; ring
    rw [q]
    apply (le_div_iff₀ (by positivity : (0:ℚ)<8*(D:ℚ))).mpr
    linarith
  have Bh : (4:ℚ)*(starWidth d:ℚ)≤μ := by
    unfold μ
    exact (le_div_iff₀ Dp).mpr (by exact_mod_cast small)
  have Hupper : (H:ℚ)≤μ+μ/8+μ/8 := by
    have hr : (H:ℚ)≤(g:ℚ)+L := by exact_mod_cast rounds.2.le
    linarith
  have avg_le : μ≤(H:ℚ) := by
    unfold μ
    apply (div_le_iff₀ Dp).mpr
    suffices M≤H*D by exact_mod_cast this
    change Nat.card E≤H*Nat.card (Cell (Fin a) G)
    rw [←exact_sum_of_fibers lab]
    calc
      _ ≤ ∑ _c : Cell (Fin a) G,H := Finset.sum_le_sum (fun c _=>(fiber_le_max lab c).trans rounds.1)
      _ = _ := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
  have hasCopy : 0<P.copies := by
    by_contra! h
    have z : P.copies=0 := by omega
    have hz : H=0 := by simp [H,fullLoad,z]
    rw [hz,Nat.cast_zero] at avg_le
    exact (not_le.mpr up avg_le)
  refine ⟨hasCopy,?_,?_⟩
  · intro c
    have h := (abs_le.mp (a_close c)).1
    have hc : (H:ℚ)+2*(starWidth d:ℚ)≤2*(Nat.card (InputCell P c):ℚ) := by linarith
    exact_mod_cast hc
  · have q : (64:ℚ)*(reciprocal d:ℚ)^2*(starWidth d:ℚ)^2*(D:ℚ)^2≤M := by
      exact_mod_cast large
    have s : (64:ℚ)*(reciprocal d:ℚ)^2*(starWidth d:ℚ)^2*(M:ℚ)≤μ^2 := by
      unfold μ
      rw [div_pow]
      apply (le_div_iff₀ (pow_pos Dp _)).mpr
      calc
        _ = ((64:ℚ)*(reciprocal d:ℚ)^2*(starWidth d:ℚ)^2*(D:ℚ)^2)*(M:ℚ) := by ring
        _ ≤ (M:ℚ)*(M:ℚ) := mul_le_mul_of_nonneg_right q (by positivity)
        _ = _ := by ring
    have bound := s.trans ((sq_le_sq₀ up.le (by positivity : (0:ℚ)≤H)).mpr avg_le)
    exact_mod_cast bound

#print axioms exact_sum_of_fibers
#print axioms actual_census_from_variance
end
end J4R43LiteralOutside

