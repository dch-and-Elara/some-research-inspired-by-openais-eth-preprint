import P5P3Decoder

/-! Exact P.1 / P.2 arithmetic conditional only on the uniformizer's
discrete membership law and the integer valuations of the displayed
center and Lagrange carrier constant. It tests a fixed decoder and
independent coefficient errors, not all decoders with the same data. -/
namespace Paper5.P3
open scoped BigOperators Polynomial

variable {K : Type*} [Field K] {T : Type*} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
theorem pow_factor {O : Subring K} (π : Kˣ) (x c : K) (A B : ℤ) (n : ℕ)
    (w z : Oˣ)
    (hx : x = (↑(π^A):K)*((w:O):K))
    (hy : c = (↑(π^B):K)*((z:O):K)) :
    x*c^n = (↑(π^(A+B*n)):K)*(((w*z^n:Oˣ):O):K) := by
  rw [hx,hy,mul_pow,zpow_add,zpow_mul,zpow_natCast]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Subring.coe_mul,Subring.coe_pow]
  ring

omit [DecidableEq T] in
theorem attained_valuation_criterion
    (O : Subring K) (π : Kˣ) (hm : ∀ n : ℤ,(↑(π^n):K)∈O ↔ 0≤n)
    (q : T→ℕ) (b : ℕ) (entry : Slot q→Fin b→Fin b→K) (P : T→ℤ) (p : ℤ)
    (M : T→K) (m : T→ℤ)
    (bound : ∀ (x : Slot q) (i j : Fin b),InLattice O (M x.1) (entry x i j))
    (attain : ∀ t,0<q t → ∃ (r : Fin (q t)) (i j : Fin b) (w : Oˣ),
      entry ⟨t,r⟩ i j = M t*((w:O):K))
    (hM : ∀ t,0<q t → ∃ w : Oˣ,M t=(↑(π^(m t)):K)*((w:O):K)) :
    Certified O q b entry (fun t => (↑(π^(P t)):K)) (↑(π^p):K) ↔
      ∀ t,0<q t → 0≤P t+m t-p := by
  rw [attained_envelope_iff O q b entry _ M _ bound attain]
  refine forall_congr' fun t => ?_
  constructor
  · intro H ht
    obtain ⟨w,hw⟩ := hM t ht
    have he : M t*(↑(π^(P t)):K) = (↑(π^(P t)):K)*(↑(π^(m t)):K)*((w:O):K) := by
      rw [hw]
      ac_rfl
    rw [he] at H
    exact (exact_scaled_generator O π hm (P t) p (m t) w).1 (H ht)
  · intro H ht
    obtain ⟨w,hw⟩ := hM t ht
    have he : M t*(↑(π^(P t)):K) = (↑(π^(P t)):K)*(↑(π^(m t)):K)*((w:O):K) := by
      rw [hw]
      ac_rfl
    rw [he]
    exact (exact_scaled_generator O π hm (P t) p (m t) w).2 (H ht)

theorem fixed_decoder_p1 (O : Subring K) (π : Kˣ)
    (hm : ∀ n : ℤ,(↑(π^n):K)∈O ↔ 0≤n)
    (u : T→K) (q : T→ℕ) (b : ℕ) (hb : 0<b)
    (P loss c : T→ℤ) (p : ℤ)
    (hn : ∀ t,u t≠0) (hi : ∀ t,(u t)⁻¹∈O) (hd : ∀ r s,(u r-u s)⁻¹∈O)
    (hu : ∀ t,0<q t → ∃ w : Oˣ,u t=(↑(π^(-loss t)):K)*((w:O):K))
    (hc : ∀ t,0<q t → ∃ w : Oˣ,carrierZero u q t=(↑(π^(c t)):K)*((w:O):K)) :
    Certified O q b (decoderEntry O u q b hd) (fun t => (↑(π^(P t)):K)) (↑(π^p):K) ↔
      ∀ t,0<q t → (↑b+↑(q t)-2)*loss t ≤ P t-p+c t := by
  let n (t : T) := (b-1)+(q t-1)
  let M (t : T) := carrierZero u q t * (u t)^(n t)
  let m (t : T) := c t + (-loss t)*(n t:ℤ)
  have hattain (t : T) (ht : 0<q t) :
      ∃ (r : Fin (q t)) (i j : Fin b) (w : Oˣ),
        decoderEntry O u q b hd ⟨t,r⟩ i j = M t*((w:O):K) := by
    refine ⟨⟨q t-1,by omega⟩,⟨0,hb⟩,⟨b-1,by omega⟩,(-(1:Oˣ))^(q t-1),?_⟩
    rw [decoder_top_constant O u q b hb t ht hn hi hd,neg_pow]
    simp only [M,n,Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,
      Subring.coe_pow,Subring.coe_neg,Subring.coe_one,pow_add]
    ring
  have hM (t : T) (ht : 0<q t) : ∃ w : Oˣ,M t=(↑(π^(m t)):K)*((w:O):K) := by
    obtain ⟨w,hw⟩ := hc t ht
    obtain ⟨z,hz⟩ := hu t ht
    exact ⟨w*z^n t,pow_factor π _ _ _ _ (n t) w z hw hz⟩
  rw [attained_valuation_criterion O π hm q b _ P p M m
    (fun x i j => decoder_envelope O u q b hn hi hd x i j) hattain hM]
  refine forall_congr' fun t => ?_
  constructor <;> intro H ht
  · have h' := H ht
    have he : (n t:ℤ)=↑b+↑(q t)-2 := by dsimp [n]; omega
    change 0≤P t+(c t+(-loss t)*(n t:ℤ))-p at h'
    rw [he,neg_mul,mul_comm (loss t)] at h'
    linarith
  · have h' := H ht
    have he : (n t:ℤ)=↑b+↑(q t)-2 := by dsimp [n]; omega
    change 0≤P t+(c t+(-loss t)*(n t:ℤ))-p
    rw [he,neg_mul,mul_comm (loss t)]
    linarith

omit [Fintype T] [DecidableEq T] in
theorem pointwise_floor_p2 {q : T→ℕ} {P loss c : T→ℤ} {p b : ℤ}
    (hl : ∀ t,0<q t → 0<loss t) :
    (∀ t,0<q t → (b+↑(q t)-2)*loss t ≤ P t-p+c t) ↔
      (∀ t,0<q t → b ≤ 2-↑(q t)+(P t-p+c t)/loss t) := by
  constructor <;> intro H t ht
  · have h := (Int.le_ediv_iff_mul_le (hl t ht)).2 (H t ht)
    omega
  · apply (Int.le_ediv_iff_mul_le (hl t ht)).1
    have h := H t ht
    omega

#print axioms attained_valuation_criterion
#print axioms fixed_decoder_p1
#print axioms pointwise_floor_p2
end Paper5.P3
