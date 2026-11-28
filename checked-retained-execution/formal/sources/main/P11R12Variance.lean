import P11R12ProbabilityMean
import P11R12Scale

namespace P11R12Variance
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11R12Probability P11R12EndpointCapacity
open P11R12Scale P11R12Coverage P11SourceGeometry OuterNodePacking
variable {K E : Type*} [LinearOrder K] [Fintype K] [Fintype E]
  [Nonempty E] [DecidableEq E] {a b n : ℕ}

noncomputable def localPicks (e : Fin n ≃ Key (Fin a) K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (right : Bool) (j : Fin n) (z : Indexed b e j) : Finset (E×Bool) :=
  pickedLocal f cap (fun _ => right) (e j) z

omit [Fintype K] [Nonempty E] in
theorem local_picks_are_actual (e : Fin n ≃ Key (Fin a) K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (right : Bool)
    (x : ∀ j, Indexed b e j) (v : E) (leg : Bool) :
    (v,leg) ∈ GuardedEndpointVariance.picked (localPicks e f cap right) x ↔
      (seat (toDraw e x) f cap (v,leg)).2.val = GuardedPacking.endpoint (2^a) right := by
  classical
  have hloc (j : Fin n) : localPicks e f cap right j (x j) =
      P11R12Choice.picked (toDraw e x) f cap (fun _ => right) (e j) := by
    unfold localPicks
    rw [picked_exact_local,toDraw_at]
  rw [GuardedEndpointVariance.picked,Finset.mem_biUnion]
  constructor
  · rintro ⟨j,_,hj⟩
    rw [hloc] at hj
    exact congrArg Fin.val (Finset.mem_filter.mp hj).2.2
  · intro h
    let k := key (f (v,leg))
    let j := e.symm k
    refine ⟨j,Finset.mem_univ _,?_⟩
    rw [hloc]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(e.apply_symm_apply k).symm,Fin.ext h⟩

omit [Fintype K] [Nonempty E] [DecidableEq E] in
theorem local_picks_cap (e : Fin n ≃ Key (Fin a) K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (right : Bool)
    (j : Fin n) (z : Indexed b e j) :
    (localPicks e f cap right j z).card ≤ Nat.card (Packet b (e j)) := by
  classical
  let x (i : Fin n) : Indexed b e i :=
    if h : i=j then h.symm ▸ z else (fun _ => false,fun _ => Equiv.refl _)
  have hx : x j=z := by simp [x]
  have hh := picked_le_packet_count (toDraw e x) f cap right (e j)
  rw [picked_exact_local,toDraw_at,hx] at hh
  exact hh

set_option maxHeartbeats 10000000 in
/-- Actual whole-type random packet sorting, with the exact elementary
draw, the common-column law, and the original uniformly padded capacity.
The resulting joint event covers every nonzero signed shift in s. -/
theorem printed_P11 (e : Fin n ≃ Key (Fin a) K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (column : ∀ v i, (f (v,false) i).2 = (f (v,true) i).2)
    (hb : 0<b) (hH : 1<b*2^a) (hK : Fintype.card K = 64)
    (hSlots : Nat.card (Page a b K)*(2:ℕ)^a ≤ 2*(2*Fintype.card E))
    (packets : Finset (Page a b K)) (s : Finset ℤ) :
    let L : ℚ := ((2:ℕ)^a:ℚ)
    let A : ℚ := (Fintype.card E:ℚ)/L^2
    1-128/L^5 ≤ RandomEndpoint.probability (PacketVariance.product (sampleWeight b e))
      (fun x => ∀ t∈s, t≠0 →
        (1-1/(b:ℚ)-1/L^2)*A ≤
          ((untouched Finset.univ (vertexOwner (seat (toDraw e x) f cap))
            (matchedColumns packets (realSlot (seat (toDraw e x) f cap))
              (realSlot (seat (toDraw e x) f cap)) t)).card:ℚ)) := by
  classical
  let L : ℚ := ((2:ℕ)^a:ℚ)
  let A : ℚ := (Fintype.card E:ℚ)/L^2
  let D : ℚ := (Nat.card (Cell (Fin a) K):ℚ)
  let M : ℕ := 2*Fintype.card E
  let act (x : ∀ j, Indexed b e j) := seat (toDraw e x) f cap
  let cp (j : Fin n) := Nat.card (Packet b (e j))
  letI : Fintype (Key (Fin a) K) := Fintype.ofEquiv (Fin n) e
  have hL : (0:ℕ)<2^a := by positivity
  have hA : 0<A := by positivity
  have hD : 0<D := by
    have hh := cells_are_Ltwelve (a:=a) hK
    unfold D
    rw [hh]
    positivity
  let d0 : Draw a b K := fun _ => (fun _ => false,fun _ => Equiv.refl _)
  obtain ⟨hs, hEq⟩ := printed_variance_scale d0 M hK hSlots
  have hRewrite : ((M:ℚ)/(2*L^2))=A := by unfold M A; push_cast; ring
  have hSum : (∑ j : Fin n, (cp j:ℚ)) =
      ∑ k : Key (Fin a) K, (Nat.card (Packet b k):ℚ) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hScale : ((b*2^a:ℕ):ℚ)*(∑ j : Fin n, (cp j:ℚ)) ≤ 64*L^3/D*A^2 := by
    rw [hSum]
    change ((b*2^a:ℕ):ℚ)*(∑ k : Key (Fin a) K, (Nat.card (Packet b k):ℚ)) ≤
      64*L^3/D*(((M:ℚ)/(2*L^2))^2) at hs
    rwa [hRewrite] at hs
  have hMean (right : Bool) : (1-1/(b:ℚ))*A ≤
      PacketVariance.avg (PacketVariance.product (sampleWeight b e))
        (fun x => ((seated Finset.univ (fun v g => act x (v,g)) right).card:ℚ)) := by
    have h := expected_actual_endpoints e f cap column right hb hH
    calc
      _ = (Fintype.card E:ℚ)*((1-1/(b:ℚ))/((2^a:ℕ):ℚ)^2) := by unfold A L; push_cast; ring
      _ ≤ _ := h
  have hScaleNative : ((b*2^a:ℕ):ℚ)*(∑ j : Fin n, (cp j:ℚ)) ≤
        64*(Nat.cast ((2:ℕ)^a) : ℚ)^3/D*A^2 := by
    simpa only [Nat.cast_pow] using hScale
  dsimp only
  have h := p11_from_product_counts (T:=Indexed b e)
    packets (fun x v r => act x (v,r)) (fun x => realSlot (act x))
      (fun x => realSlot (act x)) (fun x => vertexOwner (act x))
      (fun x => actual_cover (toDraw e x) f cap)
      (localPicks e f cap) (local_picks_are_actual e f cap)
      (sampleWeight b e) (sampleWeight_prob b e) cp (b*2^a)
      (fun i => packet_card_le_padding b (e i)) (local_picks_cap e f cap)
      s A D (b:ℚ) hA hL hD hMean hScaleNative
  exact le_of_eq_of_le hEq.symm (by simpa only [Nat.cast_pow] using h)

#print axioms local_picks_are_actual
#print axioms local_picks_cap
#print axioms printed_P11
end P11R12Variance
