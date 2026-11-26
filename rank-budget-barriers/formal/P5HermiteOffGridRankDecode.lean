import P5HermiteTransportGenericExpansion

/-! Injectivity of the ACTUAL off-grid D_t. A vector in its kernel has
CRT representative divisible by every other node power and the anchor
power. Their product exceeds the allowable degree window when b>=k_t. -/
namespace Paper5.HermiteOffGrid
open Paper5.HermiteGeneric Polynomial Matrix HermiteJetTransport
open scoped BigOperators Polynomial Classical

variable {K T : Type*} [Field K]

theorem affine_zero_iff_node_power (c α : K) (hα : α≠0) (k : ℕ) (p : K[X]) :
    scalarObserve c α k p=0 ↔ nodePower c k ∣ p := by
  let A := nodeAffine c α hα k
  have he : A (jet c k p)=scalarEncode k (scalarObserve c α k p) :=
    (nodeAffine_apply c α hα k p).trans (scalarEncode_observe c α k p).symm
  rw [←jet_zero_iff]
  constructor
  · intro h
    apply A.injective
    rw [map_zero,he,h,map_zero]
  · intro h
    apply (scalarEncode_injective k)
    rw [←he,h,map_zero,map_zero]

def extendCenters (L : Layout K T) : Option T→K
  | none => L.anchor
  | some t => L.center t

def extendOrders (L : Layout K T) (b : ℕ) : Option T→ℕ
  | none => b
  | some t => L.order t

theorem extend_centers_injective (L : Layout K T) (hOff : ∀s,L.anchor≠L.center s) :
    Function.Injective (extendCenters L) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim ((hOff j) h)
  | some i =>
    cases j with
    | none => exact False.elim ((hOff i) h.symm)
    | some j => exact congrArg Option.some (L.distinct h)

variable [Fintype T] [DecidableEq T]

theorem actual_decode_single (L : Layout K T) (b : ℕ) (t : T) (x : Fin (L.order t)→K) :
    (decodeMatrix L b t) *ᵥ x = decode L b (Pi.single t x) := by
  funext i
  have h := decode_sum L b (Pi.single t x) i
  rw [Finset.sum_eq_single t] at h
  · simpa only [Pi.single_eq_same] using h.symm
  · intro j _ hne
    rw [Pi.single_eq_of_ne hne,Matrix.mulVec_zero,Pi.zero_apply]
  · simp

theorem clipped_poly_window_zero (L : Layout K T) (b : ℕ) (t : T)
    (hOff : ∀s,L.anchor≠L.center s) (hb : L.order t≤b)
    (p : degreeLT K (∑s,L.order s))
    (hAnchor : nodePower L.anchor b ∣ p.val)
    (hOther : ∀s,s≠t→nodePower (L.center s) (L.order s) ∣ p.val) :
    p.val=0 := by
  let nodes : Finset (Option T) := Finset.univ.erase (.some t)
  let P : Option T→K[X] := fun n=>nodePower (extendCenters L n) (extendOrders L b n)
  have hdiv : (∏n∈nodes,P n) ∣ p.val := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (pairwise_coprime_X_sub_C (extend_centers_injective L hOff) hij).pow
    · intro n hn
      cases n with
      | none => exact hAnchor
      | some s =>
        have hne : (Option.some s : Option T)≠Option.some t := (Finset.mem_erase.mp hn).1
        exact hOther s (fun hs=>hne (congrArg Option.some hs))
  have hnd : (∏n∈nodes,P n).natDegree=∑n∈nodes,extendOrders L b n := by
    rw [natDegree_prod_of_monic nodes P (fun n _=>node_monic _ _)]
    simp only [P,node_natDegree]
  have hC : (∑n∈nodes,extendOrders L b n)+L.order t=b+(∑s,L.order s) := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Option T)) (extendOrders L b)
      (Finset.mem_univ (Option.some t) : Option.some t ∈ (Finset.univ : Finset (Option T)))
    change (∑n∈nodes,extendOrders L b n)+L.order t = (∑n : Option T,extendOrders L b n) at he
    rw [Fintype.sum_option] at he
    exact he
  by_contra h
  have hP : p.val.natDegree < ∑s,L.order s :=
    (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp p.property)
  have hLe := natDegree_le_of_dvd hdiv h
  rw [hnd] at hLe
  omega

set_option maxHeartbeats 15000000 in
theorem actual_decode_injective (L : Layout K T) (b : ℕ) (t : T)
    (hOff : ∀s,L.anchor≠L.center s) (hb : L.order t≤b) :
    Function.Injective (decodeMatrix L b t).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x h₀
  change decodeMatrix L b t *ᵥ x=0 at h₀
  let F := scaledHermite L.center L.distinct L.order L.scale L.nonzeroScale
  let y : (s : T)→Fin (L.order s)→K := Pi.single t x
  let p := F.symm y
  have hA : scalarObserve L.anchor L.anchorScale b p.val=0 := by
    change decode L b (Pi.single t x)=0
    rwa [←actual_decode_single]
  have hp (s : T) : scalarObserve (L.center s) (L.scale s) (L.order s) p.val = y s := by
    rw [←scaledHermite_apply L.center L.distinct L.order L.scale L.nonzeroScale p s]
    change F (F.symm y) s=_
    rw [LinearEquiv.apply_symm_apply]
  have hP := clipped_poly_window_zero L b t hOff hb p
    ((affine_zero_iff_node_power _ _ L.nonzeroAnchorScale _ _).1 hA) (fun s hne=>by
      apply (affine_zero_iff_node_power _ _ (L.nonzeroScale s) _ _).1
      rw [hp]
      simp [y,hne])
  have h := hp t
  rw [hP,map_zero] at h
  have hx : y t=x := by simp [y]
  exact hx.symm.trans h.symm

#print axioms affine_zero_iff_node_power
#print axioms extend_centers_injective
#print axioms actual_decode_single
#print axioms clipped_poly_window_zero
#print axioms actual_decode_injective
end Paper5.HermiteOffGrid
