import ExpansionGraphBase
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

namespace Reconstruction.ExpansionGraph

open Finset
open scoped BigOperators Nat

noncomputable section

private def outside {m : ℕ} (B : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    Finset (Fin m) := B.filter fun x => σ x ∉ B

private def insideEvent {m : ℕ} (T B : Finset (Fin m)) :
    Finset (Equiv.Perm (Fin m)) := univ.filter fun σ => ∀ x ∈ T, σ x ∈ B

private def extendEmbedding {m : ℕ} {T B : Finset (Fin m)} (f : T ↪ B) :
    Equiv.Perm (Fin m) := by
  classical
  let e : T ↪ Fin m := f.trans ⟨Subtype.val, Subtype.val_injective⟩
  exact e.toEquivRange.extendSubtype

private theorem extendEmbedding_apply {m : ℕ} {T B : Finset (Fin m)} (f : T ↪ B) (x : T) :
    extendEmbedding f x.val = (f x).val := by
  classical
  unfold extendEmbedding
  rw [Equiv.extendSubtype_apply_of_mem (hx := x.property)]
  rfl

private theorem insideEvent_card {m : ℕ} (T B : Finset (Fin m)) :
    (insideEvent T B).card ≤ B.card.descFactorial T.card * (m-T.card) ! := by
  classical
  let restr (σ : ↥(insideEvent T B)) : T ↪ B :=
    ⟨fun x => ⟨σ.val x.val, (mem_filter.mp σ.property).2 _ x.property⟩,
      fun _ _ he => Subtype.ext (σ.val.injective (congrArg Subtype.val he))⟩
  let fixed (σ : ↥(insideEvent T B)) : Equiv.Perm (Fin m) :=
    σ.val.trans (extendEmbedding (restr σ)).symm
  have hfix (σ : ↥(insideEvent T B)) (x : Fin m) (hx : x ∈ T) : fixed σ x = x := by
    change (extendEmbedding (restr σ)).symm (σ.val x) = x
    rw [Equiv.symm_apply_eq, extendEmbedding_apply (restr σ) ⟨x,hx⟩]
    rfl
  let rem (σ : ↥(insideEvent T B)) : Equiv.Perm ↥(Tᶜ) :=
    (fixed σ).subtypeEquiv fun x => by
      simp only [mem_compl]
      constructor
      · intro hx hv
        have hh := hfix σ _ hv
        exact hx ((fixed σ).injective hh ▸ hv)
      · intro hx hv
        apply hx
        rwa [hfix σ _ hv]
  let pack (σ : ↥(insideEvent T B)) := (restr σ, rem σ)
  have hi : Function.Injective pack := by
    intro σ τ e
    have e1 : restr σ = restr τ := congrArg Prod.fst e
    have e2 : rem σ = rem τ := congrArg Prod.snd e
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ T
    · exact congrArg (fun f : T ↪ B => (f ⟨x,hx⟩).val) e1
    · have H := congrArg (fun f : Equiv.Perm ↥(Tᶜ) => (f ⟨x,mem_compl.mpr hx⟩).val) e2
      change (extendEmbedding (restr σ)).symm (σ.val x) =
        (extendEmbedding (restr τ)).symm (τ.val x) at H
      rw [e1] at H
      exact (extendEmbedding (restr τ)).symm.injective H
  have H := Fintype.card_le_of_injective pack hi
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_perm,
    card_compl, Fintype.card_fin] using H

private theorem descFactorial_half {b m : ℕ} (hb : 2*b ≤ m) (t : ℕ) :
    (b.descFactorial t : ℝ) ≤ (1/2:ℝ)^t * (m.descFactorial t : ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hm : 2*(b-t) ≤ m-t := by omega
    have hcast : ((b-t : ℕ) : ℝ) ≤ (1/2:ℝ) * ((m-t : ℕ) : ℝ) := by
      have h' : (2:ℝ) * ((b-t : ℕ) : ℝ) ≤ ((m-t : ℕ) : ℝ) := by exact_mod_cast hm
      linarith only [h']
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, pow_succ]
    calc
      _ ≤ ((1/2:ℝ) * ((m-t : ℕ) : ℝ)) * ((1/2:ℝ)^t * (m.descFactorial t : ℝ)) :=
        mul_le_mul hcast ih (by positivity) (by positivity)
      _ = _ := by ring

private theorem insideEvent_bound {m : ℕ} (T B : Finset (Fin m)) (hb : 2*B.card ≤ m) :
    ((insideEvent T B).card : ℝ) ≤ (1/2:ℝ)^T.card * (m ! : ℕ) := by
  have ht : T.card ≤ m := by simpa using card_le_univ T
  have hmul : (((m-T.card) ! * m.descFactorial T.card : ℕ) : ℝ) = (m ! : ℕ) := by
    rw [Nat.factorial_mul_descFactorial ht]
  calc
    _ ≤ (B.card.descFactorial T.card : ℝ) * ((m-T.card) ! : ℕ) := by
      exact_mod_cast insideEvent_card T B
    _ ≤ ((1/2:ℝ)^T.card * (m.descFactorial T.card : ℝ)) * ((m-T.card) ! : ℕ) :=
      mul_le_mul_of_nonneg_right (descFactorial_half hb _) (by positivity)
    _ = _ := by
      rw [Nat.cast_mul] at hmul
      rw [mul_assoc, mul_comm (m.descFactorial T.card : ℝ), hmul]

private theorem choose_half_bound (b k : ℕ) (hk : 8*k ≤ b) :
    (b.choose k : ℝ) * (1/2:ℝ)^(b-k) ≤ (13/16:ℝ)^b := by
  have hkb : k ≤ b := by omega
  have hcoef : (1/4:ℝ)^k * (b.choose k : ℝ) ≤ (5/4:ℝ)^b := by
    rw [show (5/4:ℝ) = 1/4 + 1 by norm_num, add_pow]
    have H : (1/4:ℝ)^k * 1^(b-k) * (b.choose k : ℝ) ≤
        ∑ i ∈ range (b+1), (1/4:ℝ)^i * 1^(b-i) * (b.choose i : ℝ) :=
      single_le_sum (f := fun i => (1/4:ℝ)^i * 1^(b-i) * (b.choose i : ℝ))
        (fun i _ => by positivity) (mem_range.mpr (show k < b+1 by omega))
    simpa using H
  have h8 : (8:ℝ)^k ≤ (13/10:ℝ)^b := by
    calc
      _ ≤ ((13/10:ℝ)^8)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (13/10:ℝ)^(8*k) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hk
  have hsplit : (1/2:ℝ)^b = (1/2:ℝ)^(b-k) * (1/2:ℝ)^k := by
    rw [← pow_add, Nat.sub_add_cancel hkb]
  have hcancel : (1/4:ℝ)^k * (8:ℝ)^k * (1/2:ℝ)^k = 1 := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  calc
    _ = ((1/4:ℝ)^k * (b.choose k : ℝ) * (8:ℝ)^k) * (1/2:ℝ)^b := by
      rw [hsplit]
      linear_combination -((b.choose k : ℝ) * (1/2:ℝ)^(b-k)) * hcancel
    _ ≤ ((5/4:ℝ)^b * (13/10:ℝ)^b) * (1/2:ℝ)^b := by
      gcongr
    _ = _ := by
      rw [← mul_pow, ← mul_pow]
      norm_num

private def badPerms {m : ℕ} (B : Finset (Fin m)) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ => 8*(outside B σ).card ≤ B.card

private theorem badPerms_card {m : ℕ} (B : Finset (Fin m)) (hb : 2*B.card ≤ m) :
    ((badPerms B).card : ℝ) ≤ (13/16:ℝ)^B.card * (m ! : ℕ) := by
  classical
  let k := B.card / 8
  let t := B.card - k
  let S := B.powersetCard t
  have hcover : badPerms B ⊆ S.biUnion (fun T => insideEvent T B) := by
    intro σ hσ
    have hσ' := (mem_filter.mp hσ).2
    let I := B.filter fun x => σ x ∈ B
    have hI : I.card + (outside B σ).card = B.card :=
      card_filter_partition _ _
    obtain ⟨T, hTI, hT⟩ := exists_subset_card_eq (s := I) (n := t) (by dsimp [t,k]; omega)
    refine mem_biUnion.mpr ⟨T, mem_powersetCard.mpr ⟨hTI.trans (filter_subset ..), hT⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, fun x hx => (mem_filter.mp (hTI hx)).2⟩
  have hcount : (S.card : ℝ) = (B.card.choose k : ℝ) := by
    rw [card_powersetCard]
    exact_mod_cast (Nat.choose_symm (by dsimp [k]; omega : k ≤ B.card))
  have hk : 8*k ≤ B.card := by dsimp [k]; omega
  calc
    _ ≤ ∑ T ∈ S, ((insideEvent T B).card : ℝ) := by
      exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑ _T ∈ S, (1/2:ℝ)^t * (m ! : ℕ) := by
      apply sum_le_sum
      intro T hT
      simpa [(mem_powersetCard.mp hT).2] using insideEvent_bound T B hb
    _ = ((B.card.choose k : ℝ) * (1/2:ℝ)^t) * (m ! : ℕ) := by
      rw [sum_const, nsmul_eq_mul, hcount, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (choose_half_bound _ _ hk) (by positivity)

private def badTuples {m : ℕ} (B : Finset (Fin m)) :
    Finset (Fin 16 → Equiv.Perm (Fin m)) :=
  univ.filter fun σ => ∀ i, σ i ∈ badPerms B

private theorem badTuples_card {m : ℕ} (B : Finset (Fin m)) :
    (badTuples B).card = (badPerms B).card^16 := by
  classical
  let e : ↥(badTuples B) ≃ (Fin 16 → ↥(badPerms B)) :=
    { toFun := fun σ i => ⟨σ.val i, (mem_filter.mp σ.property).2 i⟩
      invFun := fun σ => ⟨fun i => (σ i).val, mem_filter.mpr ⟨mem_univ _, fun i => (σ i).property⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using Fintype.card_congr e

/-- Sixteen permutations suffice simultaneously for every balanced cut.
The proof counts samples directly and uses a rational bound in place of binary entropy. -/
theorem exists_expanding_permutations {m : ℕ} (hm : 0 < m) :
    ∃ σ : Fin 16 → Equiv.Perm (Fin m), ∀ B : Finset (Fin m), m ≤ 4*B.card → 2*B.card ≤ m →
      ∃ i, B.card < 8*(outside B (σ i)).card := by
  classical
  let cuts : Finset (Finset (Fin m)) := univ.filter fun B => m ≤ 4*B.card ∧ 2*B.card ≤ m
  let failed := cuts.biUnion badTuples
  let M : ℝ := ((m ! : ℕ) : ℝ)^16
  let ρ : ℝ := (13/16:ℝ)^4
  have hmpos : 0 < M := pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) _
  have hρ : 0 ≤ ρ ∧ ρ < 1/2 := by norm_num [ρ]
  have hcuts : (cuts.card : ℝ) ≤ (2:ℝ)^m := by
    have hh : cuts.card ≤ Fintype.card (Finset (Fin m)) := card_le_univ _
    rw [Fintype.card_finset, Fintype.card_fin] at hh
    exact_mod_cast hh
  have hbad (B : Finset (Fin m)) (hB : B ∈ cuts) :
      ((badTuples B).card : ℝ) ≤ ρ^m * M := by
    have hh := (mem_filter.mp hB).2
    rw [badTuples_card, Nat.cast_pow]
    calc
      _ ≤ ((13/16:ℝ)^B.card * (m ! : ℕ))^16 :=
        pow_le_pow_left₀ (by positivity) (badPerms_card B hh.2) _
      _ = ρ^(4*B.card) * M := by
        dsimp [ρ,M]
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 2
        omega
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hmpos.le
        exact pow_le_pow_of_le_one hρ.1 (hρ.2.le.trans (by norm_num)) hh.1
  have hfailed : (failed.card : ℝ) < M := calc
    _ ≤ ∑ B ∈ cuts, ((badTuples B).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _B ∈ cuts, ρ^m * M := sum_le_sum hbad
    _ ≤ (2:ℝ)^m * (ρ^m * M) := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcuts (by positivity)
    _ = ((2:ℝ)*ρ)^m * M := by rw [← mul_assoc, ← mul_pow]
    _ < M := by
      have hbase : (2:ℝ)*ρ < 1 := by norm_num [ρ]
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right (pow_lt_one₀ (by positivity) hbase hm.ne') hmpos
  have hnon : failed ≠ (univ : Finset (Fin 16 → Equiv.Perm (Fin m))) := by
    intro h
    rw [h, card_univ, Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin,
      Nat.cast_pow] at hfailed
    exact (lt_irrefl M) hfailed
  obtain ⟨σ, hσ⟩ := show ∃ σ, σ ∉ failed from by
    by_contra! hall
    exact hnon (eq_univ_of_forall hall)
  refine ⟨σ, fun B hlo hhi => ?_⟩
  by_contra! hall
  apply hσ
  apply mem_biUnion.mpr
  exact ⟨B, mem_filter.mpr ⟨mem_univ _, hlo, hhi⟩,
    mem_filter.mpr ⟨mem_univ _, fun i => mem_filter.mpr ⟨mem_univ _, hall i⟩⟩⟩

private def permutationGraph {m : ℕ} (σ : Fin 16 → Equiv.Perm (Fin m)) : SimpleGraph (Fin m) where
  Adj u v := u ≠ v ∧ ∃ i, σ i u = v ∨ σ i v = u
  symm := fun _ _ ⟨h, i, e⟩ => ⟨h.symm, i, e.symm⟩
  loopless := fun _ h => h.1 rfl

private theorem permutationGraph_degree {m : ℕ} (σ : Fin 16 → Equiv.Perm (Fin m)) (u : Fin m) :
    let G := permutationGraph σ
    letI : DecidableRel G.Adj := Classical.decRel _
    G.degree u ≤ 32 := by
  classical
  let G := permutationGraph σ
  letI : DecidableRel G.Adj := Classical.decRel _
  let f (ib : Fin 16 × Bool) := if ib.2 then σ ib.1 u else (σ ib.1).symm u
  have hs : G.neighborFinset u ⊆ univ.image f := by
    intro v hv
    obtain ⟨_, i, hi | hi⟩ := (G.mem_neighborFinset u v).mp hv
    · exact mem_image.mpr ⟨(i,true), mem_univ _, by simpa [f] using hi⟩
    · exact mem_image.mpr ⟨(i,false), mem_univ _, by simpa [f] using ((σ i).symm_apply_eq.mpr hi.symm)⟩
  exact (card_le_card hs).trans ((card_image_le).trans (by simp))

/-- The degree-32 graph before cycle replacement. Loops and repeated arcs
disappear in the simple adjacency relation. -/
theorem exists_permutation_graph {m : ℕ} (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin m), ∃ _ : DecidableRel G.Adj,
      (∀ u, G.degree u ≤ 32) ∧
      ∀ B : Finset (Fin m), m ≤ 4*B.card → 2*B.card ≤ m →
        m ≤ 32*(crossingEdges G B).card := by
  obtain ⟨σ, hσ⟩ := exists_expanding_permutations hm
  let G := permutationGraph σ
  letI : DecidableRel G.Adj := Classical.decRel _
  refine ⟨G, inferInstance, permutationGraph_degree σ, ?_⟩
  intro B hlo hhi
  obtain ⟨i, hi⟩ := hσ B hlo hhi
  have hcard : (outside B (σ i)).card ≤ (crossingEdges G B).card := by
    refine card_le_card_of_injOn (fun u => (u, σ i u)) ?_ ?_
    · intro u hu
      obtain ⟨hu, hv⟩ := mem_filter.mp hu
      exact mem_crossingEdges.mpr ⟨⟨fun he => hv (he ▸ hu), i, Or.inl rfl⟩, hu, hv⟩
    · intro _ _ _ _ h
      exact congrArg Prod.fst h
  omega

end

end Reconstruction.ExpansionGraph
