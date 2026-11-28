import V8CapacityUnifiedScalarBasis

/-! The exact original S2 weight for separate public scalar cosets.
The public shifts and depths stay part of the literal sender messages. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityFactorial V8CapacityNewtonGrid
open V8CapacityUnified.ScalarBasis
open MvPolynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

variable {O H : Type*} [CommRing O] [Fintype H]
variable (π : O)

structure PublicClass where
  center : H → O
  depth : H → ℕ

def permitted (s : PublicClass (O:=O) (H:=H)) (u : H → O) : Prop :=
  ∀ i, π^(s.depth i)∣u i-s.center i

def message (s : PublicClass (O:=O) (H:=H)) (x : H → O) : H → O :=
  fun i => s.center i+π^(s.depth i)*x i

theorem message_eq_permitted (s : PublicClass (O:=O) (H:=H)) (u : H → O) :
    permitted π s u ↔ ∃ x, u=message π s x := by
  constructor
  · intro h
    choose x hx using h
    refine ⟨x,funext fun i => ?_⟩
    unfold message
    linear_combination hx i
  · rintro ⟨x,rfl⟩ i
    exact ⟨x i,by simp [message]⟩

def weight (q : ℕ) (v : H → ℕ) (a : H → ℕ) : ℕ :=
  ∑ i : H, (v i * a i + debt q (a i))

variable {π} {q : ℕ} (D : Digits π q) (hq : 0<q)

def publicNodes (s : PublicClass (O:=O) (H:=H)) (i : H) (n : ℕ) : O :=
  s.center i+π^(s.depth i)*node D hq n

def phi (s : PublicClass (O:=O) (H:=H)) (a : H → ℕ) : MvPolynomial H O :=
  publicBasis (publicNodes D hq s) a

theorem phi_expand (s : PublicClass (O:=O) (H:=H)) (N : ℕ)
    (C : MvPolynomial H O) (hC : C.totalDegree≤N) :
    ∃ coeff : V8CapacityMonicBasis.Row H N → O,
      ∑ j : V8CapacityMonicBasis.Row H N,
        coeff j • phi D hq s (V8CapacityMonicBasis.rowDegree j)=C :=
  exact_monic_expansion (publicNodes D hq s) N C hC

theorem one_coordinate (s : PublicClass (O:=O) (H:=H)) (i : H) (n : ℕ) (x : H → O) :
    (∏ j ∈ Finset.range n, (message π s x i-publicNodes D hq s i j)) =
      π^(s.depth i*n)*newton D hq n (x i) := by
  have he (j : ℕ) :
      message π s x i-publicNodes D hq s i j=π^(s.depth i)*(x i-node D hq j) := by
    unfold message publicNodes
    ring
  simp only [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,pow_mul]
  rw [newton,Fin.prod_univ_eq_prod_range (fun j => x i-node D hq j) n]

variable [IsDomain O]
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)

theorem phi_eval_normalized (s : PublicClass (O:=O) (H:=H)) (a : H → ℕ) (x : H → O) :
    MvPolynomial.eval (message π s x) (phi D hq s a) =
      π^weight q s.depth a*tensorNorm D hq hq₂ h0 hπ a x := by
  unfold phi
  rw [basis_eval]
  simp_rw [one_coordinate D hq s, norm_factor D hq hq₂ h0 hπ,
    ← mul_assoc,← pow_add]
  simp only [weight,tensorNorm,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

include hq₂ h0 hπ in
theorem phi_eval_divisibility (s : PublicClass (O:=O) (H:=H)) (a : H → ℕ) (u : H → O)
    (hu : permitted π s u) :
    π^weight q s.depth a∣MvPolynomial.eval u (phi D hq s a) := by
  obtain ⟨x,rfl⟩ := (message_eq_permitted π s u).mp hu
  rw [phi_eval_normalized D hq hq₂ h0 hπ]
  exact dvd_mul_right _ _

#print axioms message_eq_permitted
#print axioms phi_expand
#print axioms one_coordinate
#print axioms phi_eval_normalized
#print axioms phi_eval_divisibility
end
end V8CapacityUnified.Scalar
