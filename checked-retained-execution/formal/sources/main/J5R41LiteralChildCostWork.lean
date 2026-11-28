import J5R41LiteralChildCostVisits

/-! Counts for the exact physical visit types. The outer exponent
inequality is integer and does not rely on a heuristic log bound. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes
noncomputable section
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)
variable {p : ℕ} (req : Finset (Mode i p P.mask))

abbrev GatherVisits (t : ℤ) :=
  J45Cost.WorkAddress ↥(matched P i g t) (spanAt P i req) (localColumnBits P i g)

abbrev ParityVisits (t : ℤ) :=
  (↥(matched P i g t)→Bool) ×
    (J45Parity.Bits (Tile P i × Bool) × Σ b : ColVertex P i g,localColumnBits P i g b)

def localColumnCount : ℕ := ∑ b : ColVertex P i g,2^Fintype.card (ColPort P i g b)

theorem chart_local_columns_exact :
    Nat.card (Σ b : ColVertex P i g,localColumnBits P i g b)=localColumnCount P i g := by
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun b _=>by
    change Fintype.card (ColPort P i g b→Bool) = 2^Fintype.card (ColPort P i g b)
    rw [Fintype.card_fun,Fintype.card_bool])

theorem local_column_degree_count (degree : ℕ)
    (hd : ∀ b : B,Nat.card (ParentPorts N (.inr b))≤degree) :
    localColumnCount P i g ≤ Fintype.card B * 2^degree := by
  let U := ColVertex P i g
  have h (b : U) : Fintype.card (ColPort P i g b)≤degree := by
    rw [←Nat.card_eq_fintype_card,Nat.card_congr (colPortsEquiv N b.val)]
    exact hd b.val
  calc
    _≤∑ _ : U,2^degree := Finset.sum_le_sum (fun b _=>Nat.pow_le_pow_right (by decide) (h b))
    _=Fintype.card U * 2^degree := by simp [Finset.sum_const]
    _≤_ := Nat.mul_le_mul_right _ (Fintype.card_le_of_injective _ Subtype.val_injective)

theorem span_card_exact : Nat.card (J45Cost.StateBox (spanAt P i req))=V P i req := by
  unfold V J45Cost.StateBox
  rw [Nat.card_eq_fintype_card,Fintype.card_pi]
  simp only [Fintype.card_fin]

theorem literal_full_gather_count (t : ℤ) :
    Nat.card (GatherVisits P i g req t)=2^(matched P i g t).card*V P i req*localColumnCount P i g := by
  unfold GatherVisits J45Cost.WorkAddress J45Cost.Pattern
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fun,span_card_exact P i req,chart_local_columns_exact,
     Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,
     Nat.card_eq_fintype_card (α:=↥(matched P i g t)),Fintype.card_coe,mul_assoc]

theorem literal_full_gather_bound (t : ℤ) (degree : ℕ)
    (hd : ∀ b : B,Nat.card (ParentPorts N (.inr b))≤degree) :
    Nat.card (GatherVisits P i g req t)≤
      2^(matched P i g t).card*V P i req*(Fintype.card B*2^degree) := by
  rw [literal_full_gather_count]
  exact Nat.mul_le_mul_left _ (local_column_degree_count P i g degree hd)

theorem literal_three_buffers (e : ℕ) :
    Nat.card ((Fin 3 × J45Cost.StateBox (spanAt P i req)) × Fin e)=3*V P i req*e := by
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fin,span_card_exact P i req,Nat.card_fin]

theorem literal_parity_gather_count (t : ℤ) :
    Nat.card (ParityVisits P i g t)=
      2^((matched P i g t).card+Nat.card (Tile P i×Bool))*localColumnCount P i g := by
  unfold ParityVisits J45Parity.Bits
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fun,Nat.card_fun,chart_local_columns_exact,pow_add,
     Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,
     Nat.card_eq_fintype_card (α:=↥(matched P i g t)),Fintype.card_coe,
     Nat.card_eq_fintype_card (α:=ZMod 2),ZMod.card,mul_assoc]

theorem literal_sweep_additions :
    (∑ j : Tile P i×Bool,(J45Parity.active j).toList.length) =
      Nat.card (Tile P i×Bool)*2^(Nat.card (Tile P i×Bool)-1) := by
  rw [Nat.card_eq_fintype_card]
  exact J45Parity.sweep_total_additions

theorem bounded_powers_full_outer (t : ℤ) (houter : t.natAbs=2^a-1) (hodd : i.val=0)
    (bmax : ℕ) (ok : ∀ m∈req,source P.mask i m=g ∧ m.order.val≤bmax) :
    (2^(matched P i g t).card*V P i req)^(2^a) ≤
      2^(3*Nat.card E)*(tileLen i^(bmax+1)+1)^(6*Nat.card E*(bmax+1)) := by
  let C := tileLen i^(bmax+1)+1
  let d := Nat.card (Tile P i)
  change _≤2^(3*Nat.card E)*C^(6*Nat.card E*(bmax+1))
  rw [mul_pow,←pow_mul]
  apply Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (outer_match_count P i g t houter))
  have tc := source_tile_limit P i
  have eq : D i=2^a := by simp [D,hodd]
  rw [eq] at tc
  calc
    _≤(C^(d*(bmax+1)))^(2^a) :=
      pow_le_pow_left' (actual_volume_bound P i g req bmax ok) _
    _=C^((d*2^a)*(bmax+1)) := by rw [←pow_mul]; congr 1; ac_rfl
    _≤_ := Nat.pow_le_pow_right (by dsimp [C]; positivity) (Nat.mul_le_mul_right _ tc)

#print axioms chart_local_columns_exact
#print axioms local_column_degree_count
#print axioms span_card_exact
#print axioms literal_full_gather_count
#print axioms literal_full_gather_bound
#print axioms literal_three_buffers
#print axioms literal_parity_gather_count
#print axioms literal_sweep_additions
#print axioms bounded_powers_full_outer
end
end J5R41LiteralChildCost
