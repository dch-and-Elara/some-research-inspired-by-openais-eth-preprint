import A1R43LiteralRows
import A1R43LiteralColumns
import A1R43LiteralShift
import J6R15PlantedIdentityCenter
import J6R12RepackReadNatural

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 18000000
set_option maxRecDepth 2000

/-! Read the actual signed star construction in its specified Appendix
D completed slot. The only new layout premise is that the two halves
of each simulated incidence occupy consecutive positions in one packet.
Neither the column tableau nor the resulting register weight is supplied. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Repack J6R10Integral J6R11Integral P11FullPacking
open J6R12Repack

noncomputable section

variable {V Pad : Type} [DecidableEq V] [Fintype Pad] [Fintype V]
variable (F : Finset (V×V))
local notation "N" => network F Pad
local notation "E" => Wire F Pad

def rowArg {R : Type*} [CommRing R] (K : E→E→R) (x : E→Bool) (i : E) : R :=
  ∑ j : E, if x j then K i j else 0

theorem contract_count {R : Type*} [CommRing R] (K : E→E→R)
    (hK : ∀ (x : E→Bool) (u : Occ F),
      rowArg F K x (oddWire F Pad u)= -spin (x (evenWire F Pad u)))
    (positive : ∀ v,0<GraphCutMoments.degree F v) :
    J6R10Integral.contract K (fun y => ∏ r : Row F Pad,spin (rowFlag F y r))
      (fun x => ∏ c : Col F Pad,spin (colFlag F x c)) =
      (independentCount F:R) := by
  unfold J6R10Integral.contract
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : E→Bool,(∏ v : Col F Pad,spin (colFlag F x v))*rowSum F (rowArg F K x) := by
      apply Finset.sum_congr (by ext u; simp only [Finset.mem_univ])
      intro x _
      rw [rowSum,Finset.mul_sum]
      apply Finset.sum_congr (by ext u; simp only [Finset.mem_univ])
      intro y _
      change
        ((∏ r : Row F Pad,spin (rowFlag F y r))*(∏ c : Col F Pad,spin (colFlag F x c))) *
         (∏ w : E, LiteralPortCompiler.affine (y w) (rowArg F K x w)) =
        (∏ c : Col F Pad,spin (colFlag F x c)) *
         ((∏ r : Row F Pad,spin (rowFlag F y r)) *
          (∏ w : E,LiteralPortCompiler.affine (y w) (rowArg F K x w)))
      ac_rfl
    _ = ∑ σ : V→Bool,if independent F σ then (1:R) else 0 := by
      rw [weighted_columns F positive]
      apply Finset.sum_congr (by ext u; simp only [Finset.mem_univ])
      intro σ _
      rw [rowSum_NAND]
      simp only [hK,neg_mul_neg,vertexLift_even]
      exact NAND_product_indicator F σ
    _ = _ := (independentCount_indicator F).symm

variable {a : ℕ}

omit [DecidableEq V] [Fintype Pad] [Fintype V] in
theorem finite_entry_instance_irrel {K : Type*} (d e : DecidableEq K)
    (p : ℕ) (f : ℤ[X]) (T : Atlas E K a) (r q : E) :
    @finiteEntry E K d a p f 1 T (-1) 0 r q = @finiteEntry E K e a p f 1 T (-1) 0 r q :=
  congrArg (fun j : DecidableEq K=>@finiteEntry E K j a p f 1 T (-1) 0 r q)
    (Subsingleton.elim _ _)

omit [DecidableEq V] [Fintype V] in
theorem actual_odd_row_reads_even (P : PhysicalPacking N a (Fin 64))
    (f : ℤ[X]) (p : ℕ) (d : DecidableEq (Page a P.copies (Fin 64)))
    (placed : ∀ u : Occ F,unitPredecessor P (oddWire F Pad u) (evenWire F Pad u))
    (x : E→Bool) (u : Occ F) :
    rowArg F (@finiteEntry E (Page a P.copies (Fin 64)) d a p f 1 (parentAtlas P) (-1) 0)
      x (oddWire F Pad u)= -spin (x (evenWire F Pad u)) := by
  have exactEntry (r q : E) :
      @finiteEntry E (Page a P.copies (Fin 64)) d a p f 1 (parentAtlas P) (-1) 0 r q =
        if unitPredecessor P r q then -1 else 0 :=
    (finite_entry_instance_irrel F d _ p f (parentAtlas P) r q).trans
      (actual_kernel_minus_one P f 1 p r q)
  unfold rowArg
  rw [Finset.sum_eq_single (evenWire F Pad u)]
  · rw [exactEntry,if_pos (placed u)]
    cases x (evenWire F Pad u) <;> simp [spin]
  · intro j _ h
    rw [exactEntry,if_neg (fun hx=>h (unitPredecessor_unique P _ _ _ hx (placed u)))]
    split <;> rfl
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem exact_star_parent_value (P : PhysicalPacking N a (Fin 64))
    (f : ℤ[X]) (base p : ℕ) (hb : 0<base) (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : ∀ u : Occ F,unitPredecessor P (oddWire F Pad u) (evenWire F Pad u))
    (positive : ∀ v,0<GraphCutMoments.degree F v) :
    ((parentJet P (file F f base) hf (-1)).map (reduce p f 1)).eval 0 =
      (independentCount F:Box f 1 p) := by
  letI : DecidableEq (Page a P.copies (Fin 64)) := Classical.decEq _
  rw [parentJet,network_finite]
  have R (y : E→Bool) := rowProduct_receives F f base p hb hf hd y
  have C (x : E→Bool) := colProduct_receives F f base p hb hf hd x
  have rr : reduce p f 1 ∘ rowProduct N (file F f base) hf =
      fun y=>∏ r : Row F Pad,spin (rowFlag F y r) := funext R
  have cc : reduce p f 1 ∘ colProduct N (file F f base) hf =
      fun y=>∏ c : Col F Pad,spin (colFlag F y c) := funext C
  rw [rr,cc]
  exact contract_count F _ (actual_odd_row_reads_even F P f p _ placed) positive

theorem actual_named_zero_mode (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (f : ℤ[X]) (base p : ℕ) (hb : 0<base) (hp : 0<p)
    (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : ∀ u : Occ F,unitPredecessor P (oddWire F Pad u) (evenWire F Pad u))
    (positive : ∀ v,0<GraphCutMoments.degree F v) :
    (J6R14ZeroMode.polynomial P i (-1) p (file F f base) hf).eval 0 =
      (independentCount F:Box f 1 p) := by
  rw [J6R15PlantedIdentity.zero_eq_parentJet P i (minus_one_mem_grid a)
    (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi) p hp (file F f base) hf]
  exact exact_star_parent_value F P f base p hb hf hd placed positive

theorem literal_completed_register (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (f : ℤ[X]) (base p : ℕ) (hb : 0<base) (hp : 0<p)
    (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : ∀ u : Occ F,unitPredecessor P (oddWire F Pad u) (evenWire F Pad u))
    (positive : ∀ v,0<GraphCutMoments.degree F v) :
    (∏ g : Fin 64, reduce p f 1
      (actualChildTruth P i (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi)
        p 0 (file F f base) hf 0 g))=(independentCount F:Box f 1 p) := by
  rw [← J6R14ZeroMode.polynomial_eval P i (by decide : (-1:ℤ)≠0)
    (minus_one_odd_index a i hi) p (file F f base) hf 0]
  exact actual_named_zero_mode F P i hi f base p hb hp hf hd placed positive

omit [DecidableEq V] [Fintype Pad] in
theorem independentCount_le : independentCount F≤2^(Fintype.card V) := by
  unfold independentCount
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_le_of_injective
    (fun x : {σ : V→Bool//independent F σ}=>x.val) Subtype.val_injective
  simpa only [Fintype.card_fun,Fintype.card_bool] using h

theorem exact_integer_named_register (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (f : ℤ[X]) (p : ℕ)
    (enough : Fintype.card V < p) (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : ∀ u : Occ F,unitPredecessor P (oddWire F Pad u) (evenWire F Pad u))
    (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    boxNatural f 1 p hf
      ((J6R14ZeroMode.polynomial P i (-1) p (file F f (Fintype.card V+1)) hf).eval 0) =
      independentCount F := by
  have hp : 0<p := by omega
  rw [actual_named_zero_mode F P i hi f (Fintype.card V+1) p (by omega) hp hf hd placed
      (fun v=>by rw [cubic]; decide)]
  exact boxNatural_of_nat f 1 p hf hp (by decide) hd _
    ((independentCount_le F).trans_lt (Nat.pow_lt_pow_right (by decide) enough))

#print axioms contract_count
#print axioms actual_odd_row_reads_even
#print axioms exact_star_parent_value
#print axioms actual_named_zero_mode
#print axioms literal_completed_register
#print axioms independentCount_le
#print axioms exact_integer_named_register
end
end A1R43Literal
