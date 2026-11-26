import P5AlwaysSatOriginalPhysicalDNetwork
import J6R11CollisionGreedy
import J6R11CollisionReindex
import J1PPrintedMesh
import BalancedUnion

/-! Actual Appendix D root packing, at the paper's s=n+m for (M.7).
The mesh's stronger dyadic slack is used rather than the generic 2M cap:
the selected-coordinate marked law is bounded by 40/64, not 80/64. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
open J6R10Repack J6R11CollisionReindex J9PrintedSchedule J1PPrinted P11FullPacking
open J1MainSourceCollision

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

noncomputable def dLambda : ℕ := Nat.clog 2 (dSize E T)
noncomputable def dU : ℕ := rootU (dLambda E T)
noncomputable def dA : ℕ := rootA (dLambda E T)
noncomputable def dDelta : ℕ := sourceDelta (dSize E T)
noncomputable def dCells : ℕ := arrayCard (dA E T)

theorem d_cells_exact : Nat.card (Cell (Fin (dA E T)) (Fin 64))=dCells E T := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Fin (dA E T)→Fin 64×Fin 64)=64^(2*dA E T)
  rw [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,←pow_two,←pow_mul]

theorem d_root_mesh [DecidableEq V] (hC : ∀ v,GraphCutMoments.degree E v=3)
    (hU : 3≤dU E T) :
    leafThreshold (dSize E T) (dLambda E T)<dWires E T ∧
      3≤dDelta E T ∧
      2*(dCells E T)^2*dDelta E T≤dWires E T ∧
      2^(dA E T)*dCells E T≤dWires E T ∧
      (80:ℕ)^2*(dCells E T)^2*2*dDelta E T≤dWires E T := by
  have hd : 131072≤dLambda E T := by
    have h := (rootU_range (dLambda E T)).1
    change 131072*dU E T≤dLambda E T at h
    omega
  have hi : 0<(dLambda E T).sqrt := Nat.sqrt_pos.mpr (by omega)
  have hs : dSize E T<dWires E T := by
    have he := d_size_exact E T hC
    have hw := d_wire_exact E T (fun _=>false) hC
    omega
  have ha : leafThreshold (dSize E T) (dLambda E T)<dWires E T := by
    apply lt_of_le_of_lt _ hs
    change (dSize E T+(dLambda E T).sqrt-1)/(dLambda E T).sqrt≤dSize E T
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hi).2
    have hm : dSize E T≤dSize E T*(dLambda E T).sqrt :=
      by simpa using Nat.mul_le_mul_left (dSize E T) hi
    change dSize E T+(dLambda E T).sqrt-1 < (dSize E T+1)*(dLambda E T).sqrt
    rw [Nat.add_mul,one_mul]
    omega
  have hOne : 1≤rootU (Nat.clog 2 (dSize E T)) := le_trans (by decide) hU
  have hp := source_packing_conditions (dSize E T) (dWires E T) 0 hOne ha
  have hm := mesh_margins (dSize E T) (dWires E T) 0 hOne ha
  have hA : stepA (dLambda E T) 0=dA E T := by simp [dA,rootA,stepA,stepU_as_div]
  change 2*(arrayCard (stepA (dLambda E T) 0))^2*dDelta E T≤dWires E T ∧
      2^(stepA (dLambda E T) 0)*arrayCard (stepA (dLambda E T) 0)≤dWires E T ∧
      2*2^(stepA (dLambda E T) 0)≤dDelta E T at hp
  rw [hA] at hp
  have hmargin := hm.2.2.2.1
  change (((2:ℕ)^(dU E T))*2^(stepA (dLambda E T) 0)*
      arrayCard (stepA (dLambda E T) 0))^2*2*dDelta E T≤dWires E T at hmargin
  rw [hA] at hmargin
  have hA6 : 6≤dA E T := by change 6≤2*dU E T; omega
  have h64 : 64≤(2:ℕ)^(dA E T) := Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) hA6
  have h8 : 8≤(2:ℕ)^(dU E T) := Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) hU
  have h80 : 80≤(2:ℕ)^(dU E T)*2^(dA E T) :=
    (by decide : 80≤8*64).trans (Nat.mul_le_mul h8 h64)
  have hx : 80^2*(dCells E T)^2 ≤
    (((2:ℕ)^(dU E T))*2^(dA E T)*arrayCard (dA E T))^2 := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h80 2)
  refine ⟨ha,by omega,hp.1,hp.2.1,?_⟩
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hx)).trans hmargin

private theorem le_of_sq_le_sq {a b : ℚ} (hb : 0≤b) (h : a^2≤b^2) : a≤b := by
  by_contra! hc
  have hpos := mul_pos (sub_pos.mpr hc) (show 0<a+b by linarith only [hb,hc])
  nlinarith only [h,hpos]

theorem d_cell_cap [DecidableEq V] (hC : ∀ v,GraphCutMoments.degree E v=3)
    (hT : T.card≤Fintype.card V/4) (hN : 16≤Fintype.card V) (hU : 3≤dU E T)
    (P : PhysicalPacking (dNetwork E T) (dA E T) (Fin 64))
    (hVar : varianceScore (declaredCell (dNetwork E T) P.rowLabel P.colLabel)≤
      2*(dWires E T:ℚ)*dDelta E T)
    (c : Cell (Fin (dA E T)) (Fin 64)) :
    (Nat.card (J6R10Repack.Fiber (declaredCell (dNetwork E T) P.rowLabel P.colLabel) c):ℚ) ≤
      40*(Fintype.card V:ℚ)/dCells E T := by
  let M : ℚ := dWires E T
  let D : ℚ := dCells E T
  let Δ : ℚ := dDelta E T
  let N : ℚ := Fintype.card V
  let load : ℚ := Nat.card (J6R10Repack.Fiber
    (declaredCell (dNetwork E T) P.rowLabel P.colLabel) c)
  have hD : 0<D := by dsimp [D,dCells,arrayCard]; positivity
  have hM : 0≤M := by dsimp [M]; positivity
  have hsq : (load-M/D)^2≤2*M*Δ := by
    have h := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun c : Cell (Fin (dA E T)) (Fin 64)=>
        ((Nat.card (J6R10Repack.Fiber (declaredCell (dNetwork E T) P.rowLabel P.colLabel) c):ℚ)-
          (Nat.card (DWire E T):ℚ)/Nat.card (Cell (Fin (dA E T)) (Fin 64)))^2)
      (fun _ _=>sq_nonneg _) (Finset.mem_univ c)
    change _≤varianceScore _ at h
    rw [d_cells_exact,Nat.card_eq_fintype_card] at h
    exact h.trans hVar
  have hMargin : (80:ℚ)^2*D^2*2*Δ≤M := by
    dsimp [M,D,Δ]
    exact_mod_cast (d_root_mesh E T hC hU).2.2.2.2
  have hStep : (80*(load*D-M))^2≤M^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hsq
      (show 0≤(80:ℚ)^2*D^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hMargin hM
    have hEq : (load-M/D)*D = load*D-M := by
      rw [sub_mul,div_mul_cancel₀ _ hD.ne']
    rw [←hEq,mul_pow,mul_pow]
    nlinarith only [h₁,h₂]
  have hStep' := le_of_sq_le_sq hM hStep
  have hm39 := (show M≤39*N+8 by dsimp only [M,N]; exact_mod_cast d_wire_quarter_upper E T hC hT)
  have hn16 : (16:ℚ)≤N := by dsimp only [N]; exact_mod_cast hN
  change load≤40*N/D
  apply (le_div_iff₀ hD).mpr
  linarith only [hStep',hm39,hn16]

set_option maxHeartbeats 1500000 in
theorem d_actual_packing [DecidableEq V] (hC : ∀ v,GraphCutMoments.degree E v=3)
    (hT : T.card≤Fintype.card V/4) (hN : 16≤Fintype.card V) (hU : 3≤dU E T) :
    ∃ P : PhysicalPacking (dNetwork E T) (dA E T) (Fin 64),
      P.copies=ceilCopies (2^dA E T) (maxFiber (declaredCell (dNetwork E T) P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell (dNetwork E T) P.rowLabel P.colLabel)≤
        2*(dWires E T:ℚ)*dDelta E T ∧
      ∀ c : Cell (Fin (dA E T)) (Fin 64),
        (Nat.card (J6R10Repack.Fiber (declaredCell (dNetwork E T) P.rowLabel P.colLabel) c):ℚ) ≤
          40*(Fintype.card V:ℚ)/dCells E T := by
  have h := d_root_mesh E T hC hU
  obtain ⟨z,hz⟩ := J6R11CollisionGreedy.labels_by_conditioning
    (A:=Fin (dA E T)→Fin 64) (dNetwork E T).row (dNetwork E T).col (dDelta E T)
    (fun v=>by rw [card_filter_fibre]; exact (d_row_degree_le E T v).trans h.2.1)
    (fun v=>by rw [card_filter_fibre,d_subdivision_degree]; omega)
  have hs : varianceScore (declaredCell (dNetwork E T) z.1 z.2) ≤
      2*(Nat.card (DWire E T):ℚ)*dDelta E T := by
    rwa [declared_variance_eq (dNetwork E T) z,Nat.card_eq_fintype_card]
  obtain ⟨P,hr,hc,hP⟩ := actual_rounded_packing (dNetwork E T) (by simp)
    z.1 z.2 (dDelta E T) hs
    (by rw [Nat.card_eq_fintype_card]; exact h.2.2.1)
    (by rw [Nat.card_eq_fintype_card]; exact h.2.2.2.1)
  have hfinal : varianceScore (declaredCell (dNetwork E T) P.rowLabel P.colLabel)≤
      2*(dWires E T:ℚ)*dDelta E T := by
    rw [hr,hc]
    simpa only [Nat.card_eq_fintype_card] using hs
  exact ⟨P,by rw [hr,hc,hP],hfinal,d_cell_cap E T hC hT hN hU P hfinal⟩

theorem d_mesh_threshold_from_N [DecidableEq V]
    (hC : ∀ v,GraphCutMoments.degree E v=3)
    (hN : 393216≤Nat.clog 2 (Fintype.card V)) : 3≤dU E T := by
  have hLambda : 393216≤dLambda E T := hN.trans
    (Nat.clog_mono_right 2 (d_size_and_wire_range E T hC).1)
  change 3≤dLambda E T/(128*1024)
  omega

#print axioms d_cells_exact
#print axioms d_root_mesh
#print axioms d_cell_cap
#print axioms d_actual_packing
#print axioms d_mesh_threshold_from_N
end Paper5.AlwaysSatOriginal.Physical