import AffineEdge
import AffineEdgeAffine
import AffineEdgeEncoderData

open scoped BigOperators Polynomial

namespace AffineEdge

noncomputable section

variable {q : ℕ} {F : Type*} [Field F]

private def bucketProjection (a : Bits q) (b : Fin ((q+1)/2)) :
    (EncoderRow q → F) →ₗ[F] F :=
  LinearMap.proj (.inr (.inl b)) -
    ∑ s : Fin q, (if bucket s = b then bitScalar (R := F) (a s) else 0) • LinearMap.proj (.inl s)

private theorem bucketProjection_column (a c : Bits q) (b : Fin ((q+1)/2)) (k : Kind q) :
    bucketProjection (F := F) a b (encoderColumn c k) =
      match k with
      | none => 0
      | some s => if bucket s = b then bitScalar (c s) - bitScalar (a s) else 0 := by
  cases k with
  | none =>
    simp only [bucketProjection, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, encoderColumn, mul_zero, Finset.sum_const_zero, sub_zero]
  | some s =>
    simp only [bucketProjection, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, encoderColumn, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : bucket s = b
    · simp [h]
    · simp [h, Ne.symm h]

private theorem bit_delta_ne (b : Bool) : bitScalar (R := F) (!b) - bitScalar b ≠ 0 := by
  cases b <;> simp [bitScalar]

private theorem bucket_two {s t u : Fin q} (hs : bucket s = bucket t) (hu : bucket u = bucket t)
    (hst : s ≠ t) (hut : u ≠ t) : s = u := by
  have hs' := congrArg Fin.val hs
  have hu' := congrArg Fin.val hu
  change s.val/2 = t.val/2 at hs'
  change u.val/2 = t.val/2 at hu'
  have ht' : s.val ≠ t.val := fun h => hst (Fin.ext h)
  have hu'' : u.val ≠ t.val := fun h => hut (Fin.ext h)
  apply Fin.ext
  omega

private theorem bucket_moments {slope : Fin q → F} (hi : Function.Injective slope)
    (z : Fin q → F) (t : Fin q)
    (h₀ : (∑ s, if bucket s = bucket t then z s else 0) = 0)
    (h₁ : (∑ s, if bucket s = bucket t then slope s * z s else 0) = 0) :
    z t = 0 := by
  classical
  let S := Finset.univ.filter (fun s => bucket s = bucket t)
  have ht : t ∈ S := by simp [S]
  have h₀' : (∑ s ∈ S, z s) = 0 := by simpa [S, Finset.sum_filter] using h₀
  have h₁' : (∑ s ∈ S, slope s * z s) = 0 := by simpa [S, Finset.sum_filter] using h₁
  rw [← Finset.sum_erase_add S z ht] at h₀'
  rw [← Finset.sum_erase_add S (fun s => slope s*z s) ht] at h₁'
  by_cases he : (S.erase t).Nonempty
  · obtain ⟨u, hu⟩ := he
    have hU : S.erase t = {u} := by
      ext s
      simp only [Finset.mem_singleton]
      constructor
      · intro hs
        exact bucket_two (Finset.mem_filter.mp (Finset.mem_of_mem_erase hs)).2
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).2
          (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase hu)
      · rintro rfl
        exact hu
    rw [hU, Finset.sum_singleton] at h₀' h₁'
    have hp : (slope t - slope u) * z t = 0 := by
      calc
        _ = (slope u * z u + slope t * z t) - slope u * (z u + z t) := by ring
        _ = 0 := by rw [h₀', h₁', mul_zero, sub_zero]
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr
      (fun h => Finset.ne_of_mem_erase hu (hi h).symm))
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, zero_add] at h₀'
    exact h₀'

private theorem encoder_centerCondition (slope : Fin q → F) (hi : Function.Injective slope) :
    CenterCondition slope (encoderColumn (F := F)) := by
  classical
  intro a x hx k
  have hm (b : Fin ((q+1)/2)) :
      (∑ t, if bucket t = b then x (targetSlot (some t)) *
        (bitScalar (R := F) (!(a t)) - bitScalar (a t)) else 0) = 0 ∧
      (∑ t, if bucket t = b then slope t * (x (targetSlot (some t)) *
        (bitScalar (R := F) (!(a t)) - bitScalar (a t))) else 0) = 0 := by
    let φ := bucketProjection (F := F) a b
    have hc (p : Kind q × Bool) : φ ((centerVector encoderColumn a p).1) = 0 ∧
        φ ((centerVector encoderColumn a p).2) = 0 := by
      rcases p with ⟨k,p⟩
      cases p <;> cases k <;> simp [φ, centerVector, bucketProjection_column]
    have hn (t : Fin q) (k : Kind q) :
        φ (encoderColumn (flip t a) k) =
          if k = some t ∧ bucket t = b then
            bitScalar (!(a t)) - bitScalar (a t) else 0 := by
      cases k with
      | none => simp [φ, bucketProjection_column]
      | some s =>
        by_cases he : s = t
        · subst s
          simp [φ, bucketProjection_column]
        · simp [φ, bucketProjection_column, he]
    let δ (t : Fin q) := bitScalar (R := F) (!(a t)) - bitScalar (a t)
    have hfirst (t : Fin q) :
        (∑ k : Kind q, x (.inr (t,k)) * φ (encoderColumn (flip t a) k)) =
          if bucket t = b then x (.inr (t,some t)) * δ t else 0 := by
      by_cases hb : bucket t = b
      · simp [hn, hb, δ, mul_ite]
      · simp [hn, hb]
    have hsecond (t : Fin q) :
        (∑ k : Kind q, x (.inr (t,k)) * (slope t * φ (encoderColumn (flip t a) k))) =
          if bucket t = b then slope t * (x (.inr (t,some t)) * δ t) else 0 := by
      simp only [mul_left_comm (x _) (slope t), ← Finset.mul_sum, hfirst, mul_ite, mul_zero]
    have hc₀ (p : Kind q × Bool) : φ ((centerVector encoderColumn a p).1) = 0 := (hc p).1
    have hc₁ (p : Kind q × Bool) : φ ((centerVector encoderColumn a p).2) = 0 := (hc p).2
    have h := congrArg (φ.prodMap φ) hx
    simp only [map_zero, Fintype.sum_sum_type] at h
    constructor
    · have h' := congrArg Prod.fst h
      simpa only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero,
        LinearMap.prodMap_apply, map_add, map_sum, map_smul, slotColumn_center,
        hc₀, smul_zero, Finset.sum_const_zero,
        zero_add, Fintype.sum_prod_type, slotColumn_neighbor, affineVector, smul_eq_mul, mul_zero,
        hfirst, δ, targetSlot] using h'
    · have h' := congrArg Prod.snd h
      simpa only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero,
        LinearMap.prodMap_apply, map_add, map_sum, map_smul, slotColumn_center,
        hc₁, smul_zero, Finset.sum_const_zero,
        zero_add, Fintype.sum_prod_type, slotColumn_neighbor, affineVector,
        smul_eq_mul, mul_zero, hsecond, δ, targetSlot] using h'
  cases k with
  | some t =>
    let z (s : Fin q) := x (targetSlot (some s)) *
      (bitScalar (R := F) (!(a s)) - bitScalar (a s))
    exact (mul_eq_zero.mp (bucket_moments hi z t (hm (bucket t)).1 (hm (bucket t)).2)).resolve_right
      (bit_delta_ne (a t))
  | none =>
    let j : EncoderRow q := .inr (.inr (parity a))
    have h := congrArg (fun z : (EncoderRow q → F) × (EncoderRow q → F) => z.1 j) hx
    have hc (p : Kind q × Bool) :
        (centerVector (encoderColumn (F := F)) a p).1 j =
          if p = (none,false) then 1 else 0 := by
      rcases p with ⟨k,b⟩
      cases k <;> cases b <;> simp [centerVector, j, encoderColumn]
    have hn (t : Fin q) (k : Kind q) : encoderColumn (F := F) (flip t a) k j = 0 := by
      cases k <;> simp [encoderColumn, j, (parity_flip a t).symm]
    simpa [Fintype.sum_sum_type, Fintype.sum_prod_type, slotColumn_center, slotColumn_neighbor,
      Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, hc, hn, affineVector, mul_ite, Finset.sum_ite_eq', targetSlot] using h

theorem binaryEncoder_attains (sites : Fin q → F) (hq : 2 ≤ q)
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    (∃ P, PairedCondition sites (binaryEncoder q) (q-2) P) ∧
      (binaryEncoder (F := F) q).rank = q + (q+1)/2 + 2 := by
  have hs : Function.Injective (fun t => -(sites t)⁻¹) :=
    fun _ _ h => hi (inv_injective (neg_injective h))
  have hc : CenterCondition (fun t => -(sites t)⁻¹)
      (fun a k j => binaryEncoder (F := F) q j (hardWord a k)) := by
    simpa only [binaryEncoder_hardWord] using encoder_centerCondition _ hs
  obtain ⟨P, hP⟩ := paired_of_affine hq hn
    (affine_of_centerCondition hi hn binaryEncoder_zero_other hc)
  refine ⟨⟨P,hP⟩, le_antisymm ?_ (paired_rank_lower hq hi hn hP)⟩
  simpa [EncoderRow, Nat.add_assoc] using (binaryEncoder (F := F) q).rank_le_card_height

end
end AffineEdge
