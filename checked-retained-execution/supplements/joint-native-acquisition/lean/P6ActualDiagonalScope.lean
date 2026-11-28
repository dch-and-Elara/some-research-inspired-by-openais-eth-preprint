import P6ActualDiagonal
import P6ActualCauchy
import J6R9PacketRealTile

open scoped Polynomial BigOperators Classical
open P11FullPacking P1DyadicGrid NativeProbeRing
namespace P6Joint
noncomputable section
variable {K E : Type*} [Fintype E] [LinearOrder K] {a b : ℕ}
/-- For an actual dense physical diagonal page, every real ordered
row/column pair has one and the same native group and a nonzero literal
Cauchy coefficient in the receiver ring. The labels/roster are not
reselected. The input density certificate is explicit. -/
theorem diagonal_page_native_scope
    (mask : MaskFamily a b K) (seat : E ↪ Physical a b K)
    (word : Fin a → K) (hb : 0<b) (r : ℕ)
    (enough : b*r ≤ (Finset.univ.filter (fun e => physicalCell mask (seat e) = diagCell word)).card)
    (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (hprec : a+1<p) (t : ℤ) (ht : t ∈ grid a)
    (z : Scalar p f) (hz : IsUnit z) (i : Fin a)
    {V : Type*} [DecidableEq V] (colVertex : E → V)
    (bounded : ∀ v, ((Finset.univ : Finset E).filter (fun e => colVertex e = v)).card ≤ 3) :
    ∃ packet : Packet b (key (diagCell word)),
      let live := (Finset.univ : Finset E).filter (fun e => (seat e).1 = ⟨key (diagCell word),packet⟩)
      r ≤ 3*(live.image colVertex).card ∧
      (∀ x ∈ live, ∀ y ∈ live,
        ((physicalCell mask (seat x)) i).1 = ((physicalCell mask (seat y)) i).2 ∧
        (J6R9PacketLocal.W a t (((seat y).2.val:ℤ)-((seat x).2.val:ℤ))).eval₂
          (J6ZeroTransport.reduceAt p (scalar_nilpotent p f)) z ≠ 0) := by
  classical
  obtain ⟨packet, hDense⟩ := exists_dense_actual_diagonal_page mask seat word hb r enough
  refine ⟨packet, ?_⟩
  dsimp only
  let live := (Finset.univ : Finset E).filter (fun e => (seat e).1 = ⟨key (diagCell word),packet⟩)
  have liveBound (v : V) : (live.filter (fun e => colVertex e = v)).card ≤ 3 :=
    (Finset.card_le_card (fun _ h => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩)).trans (bounded v)
  refine ⟨hDense.trans (surviving_ports_le_three_scope live colVertex liveBound), ?_⟩
  have hcell (x : E) (hx : x ∈ live) : physicalCell mask (seat x) = diagCell word := by
    have h := (Finset.mem_filter.mp hx).2
    have hpair : seat x = (⟨key (diagCell word),packet⟩,(seat x).2) := Prod.ext h rfl
    rw [hpair]
    exact diagonal_cell_uniform word mask packet _
  intro x hx y hy
  refine ⟨?_,actual_cauchy_survives_unit p f hf hd ht
    (J6R9PacketRealTile.difference_mem_grid (seat x).2 (seat y).2) hprec z hz⟩
  rw [hcell x hx,hcell y hy]
  rfl

/-- Specialization to the exact J9 receiver precision and extreme mesh
center. Nonzero addresses are the original binary-coordinate words. -/
theorem extreme_diagonal_10M_of_density
    (mask : MaskFamily a b K) (seat : E ↪ Physical a b K)
    (word : Fin a → K) (hb : 0<b) (r : ℕ)
    (enough : b*r ≤ (Finset.univ.filter (fun e => physicalCell mask (seat e) = diagCell word)).card)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))]
    (hprec : a+1 < 10 * Fintype.card E)
    (i : Fin a) {V : Type*} [DecidableEq V] (colVertex : E → V)
    (bounded : ∀ v, ((Finset.univ : Finset E).filter (fun e => colVertex e = v)).card ≤ 3) :
    ∃ packet : Packet b (key (diagCell word)),
      let live := (Finset.univ : Finset E).filter (fun e => (seat e).1 = ⟨key (diagCell word),packet⟩)
      let p := 10*Fintype.card E
      r ≤ 3*(live.image colVertex).card ∧
      (∀ x ∈ live, ∀ y ∈ live, ∀ addr : Fin f.natDegree → Bool, addr ≠ (fun _ => false) →
        ((physicalCell mask (seat x)) i).1 = ((physicalCell mask (seat y)) i).2 ∧
        (J6R9PacketLocal.W a (pow₂ a - 1) (((seat y).2.val:ℤ)-((seat x).2.val:ℤ))).eval₂
          (J6ZeroTransport.reduceAt p (scalar_nilpotent p f)) (probe p f addr) ≠ 0) := by
  classical
  obtain ⟨packet, hDense⟩ := exists_dense_actual_diagonal_page mask seat word hb r enough
  refine ⟨packet, ?_⟩
  dsimp only
  let live := (Finset.univ : Finset E).filter (fun e => (seat e).1 = ⟨key (diagCell word),packet⟩)
  have liveBound (v : V) : (live.filter (fun e => colVertex e = v)).card ≤ 3 :=
    (Finset.card_le_card (fun _ h => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩)).trans (bounded v)
  refine ⟨hDense.trans (surviving_ports_le_three_scope live colVertex liveBound), ?_⟩
  have hcell (x : E) (hx : x ∈ live) : physicalCell mask (seat x) = diagCell word := by
    have h := (Finset.mem_filter.mp hx).2
    have hpair : seat x = (⟨key (diagCell word),packet⟩,(seat x).2) := Prod.ext h rfl
    rw [hpair]
    exact diagonal_cell_uniform word mask packet _
  have ht : pow₂ a - 1 ∈ grid a := by
    rw [mem_grid]
    have hh := pow₂_pos a
    omega
  intro x hx y hy addr haddr
  refine ⟨?_,actual_cauchy_survives_unit _ f hf hd ht
    (J6R9PacketRealTile.difference_mem_grid (seat x).2 (seat y).2) hprec _
    (nonzero_binary_probe_unit _ (by omega) f hf hd addr haddr)⟩
  rw [hcell x hx,hcell y hy]
  rfl

#print axioms extreme_diagonal_10M_of_density

#print axioms diagonal_page_native_scope

end
end P6Joint