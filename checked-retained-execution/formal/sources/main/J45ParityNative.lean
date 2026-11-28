import J45Parity
import J45ParityDP

/-! Actual all/odd tile feature payloads, how repeated powers are compressed,
and an operation count for reading them from the original local columns. -/
namespace J45Parity
open scoped BigOperators Classical

section Source

variable {B T : Type*} [Fintype B] [Fintype T] [DecidableEq T]
  {Q : B→Type*} [∀ b,Fintype (Q b)]

/-- False is the sum of all occupied bits in a tile; true only odd positions. -/
def localFeature (tile : ∀ b,Q b→T) (index : ∀ b,Q b→ℕ) (b : B)
    (z : Q b→Bool) (f : T×Bool) : ZMod 2 :=
  ∑ q : Q b, if tile b q=f.1 ∧ z q=true then
    (if f.2 then (index b q : ZMod 2) else 1) else 0

omit [Fintype B] [Fintype T] in
theorem localMode_feature (tile : ∀ b,Q b→T) (index : ∀ b,Q b→ℕ) (b : B)
    (z : Q b→Bool) (τ : T) (n : ℕ) :
    (∑ q : Q b, if tile b q=τ ∧ z q=true then (index b q : ZMod 2)^n else 0) =
      localFeature tile index b z (τ,decide (n≠0)) := by
  unfold localFeature
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hn : n=0
  · simp [hn]
  · simp [hn,JointContraction.parity_pos_pow _ (Nat.pos_of_ne_zero hn)]

abbrev PayloadVisits (T : Type*) (Q : B→Type*) :=
  Σ b, (Q b→Bool) × ((T×Bool) × Q b)

omit [DecidableEq T] in
/-- A (deliberately dense) scan constructs every payload statistic from
the actual original ports; the overall bound also charges its repetition
for each matched pattern if it is not cached. -/
theorem payload_visits :
    Fintype.card (PayloadVisits T Q) =
      ∑ b, 2^Fintype.card (Q b) * ((2*Fintype.card T)*Fintype.card (Q b)) := by
  classical
  simp [Nat.mul_comm]

end Source

section Powers

variable {D J : Type*} [DecidableEq D]

/-- Collapse repeated occurrences and positive powers of the same actual
feature. Zero powers do not contribute any requested address. -/
theorem collapse_powers (s : Finset J) (which : J→D) (exponent : J→ℕ) (x : D→ZMod 2) :
    (∏ j∈s, x (which j) ^ exponent j) =
      ∏ d∈(s.filter (fun j => 0<exponent j)).image which, x d := by
  classical
  by_cases h : ∃ j∈s, 0<exponent j ∧ x (which j)=0
  · obtain ⟨j,hj,hpow,hx⟩ := h
    have hmem : which j ∈ (s.filter (fun k => 0<exponent k)).image which := by
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hpow⟩,rfl⟩
    rw [Finset.prod_eq_zero hj (by simp [hx,Nat.ne_of_gt hpow]), Finset.prod_eq_zero hmem hx]
  · have h1 : ∀ j∈s, 0<exponent j → x (which j)=1 := by
      intro j hj hp
      have hn : x (which j)≠0 := fun h0 => h ⟨j,hj,hp,h0⟩
      generalize hX : x (which j)=v at hn ⊢
      fin_cases v <;> simp_all
    have hl : (∏ j∈s, x (which j) ^ exponent j) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      by_cases hp : 0<exponent j
      · simp [h1 j hj hp]
      · simp [show exponent j=0 by omega]
    have hr : (∏ d∈(s.filter (fun j => 0<exponent j)).image which, x d)=1 := by
      apply Finset.prod_eq_one
      intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      exact h1 j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    rw [hl,hr]

end Powers

section CompleteMenu

open JointContraction
variable {A B M T : Type*} [Fintype A] [Fintype B] [Fintype M]
  [Fintype T] [DecidableEq T] {P : A→Type*} {Q : B→Type*}
  [∀ a,Fintype (P a)] [∀ b,Fintype (Q b)]

/-- Compose the costed in-place transform, finite parity DP and the original
literal row sum. The input to run is constructed, not an external oracle. -/
theorem native_parity_menu (s : List B) (hs : s.Nodup) (full : s.toFinset=Finset.univ)
    (ports : M→Sigma Q) (wire : ∀ a,P a→Option M) (unit : ZMod 2)
    (tabA : ∀ a,(P a→Bool)→ZMod 2) (tabB : ∀ b,(Q b→Bool)→ZMod 2)
    (tile : ∀ b,Q b→T) (index : ∀ b,Q b→ℕ) (S : Finset (T×Bool)) :
    run (buildTable s ports wire unit tabA tabB (localFeature tile index))
        (Finset.univ : Finset (T×Bool)).toList S =
     ∑ x : (∀ b,Q b→Bool), ∑ y : (∀ a,P a→Bool),
      ((∏ a,tabA a (y a)) * ∏ a,∏ p,
        literal (y a p) (wiredInput unit (matchedBits ports x) (wire a p))) *
      ((∏ b,tabB b (x b)) * (∏ d∈S,(∑ b,localFeature tile index b (x b)) d)) := by
  rw [all_moments]
  exact buildTable_superset s hs full ports wire unit tabA tabB _ S

end CompleteMenu

#print axioms localMode_feature
#print axioms payload_visits
#print axioms collapse_powers
#print axioms native_parity_menu

end J45Parity