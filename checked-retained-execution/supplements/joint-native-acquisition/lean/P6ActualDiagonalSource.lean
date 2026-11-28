import P6ActualDiagonalScope

open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking P1DyadicGrid NativeProbeRing
open J7SeatPacking J7SeatSource J7FullWordCells J7FullWordAssembly J7SourceLabels J7SourceConditioning
namespace P6Joint
noncomputable section

variable {A Pair Row Col W : Type*} [LinearOrder A] [Fintype A]
  [Fintype Pair] [Fintype W] {a b : ℕ}

theorem extreme_diagonal_10M_from_source_certificate (row : W → Row)
    (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin a → A) Pair Row Col) (hz : ∀ d, 0 < weight d (z d))
    (seat : Wire Pair W ↪ Physical (a+1) b A)
    (seat_eq : ∀ w, physicalCell (balancedMask (a+1) b) (seat w) = wordLabel row col z w)
    (word : Fin (a+1) → A) (hb : 0<b) (dev : ℚ) (he : 0≤dev)
    (hdev : ∀ c, ((∑ w : Wire Pair W, indicator (fullCell row col w z) c) -
      (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin a → A))^2 ≤ dev^2)
    (hp : (b:ℚ)*2^(a+1) ≤ (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin a → A) + dev + 2^(a+1))
    (hbig : 3*dev+2^(a+1) ≤ (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin a → A))
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))]
    (hprec : a+2 < 10 * Fintype.card (Wire Pair W))
    (i : Fin (a+1)) [DecidableEq Col] [DecidableEq Pair]
    (bounded : ∀ v, ((Finset.univ : Finset (Wire Pair W)).filter (fun e => colNode col e = v)).card ≤ 3) :
    ∃ packet : Packet b (key (diagCell word)),
      let live := (Finset.univ : Finset (Wire Pair W)).filter
        (fun e => (seat e).1 = ⟨key (diagCell word),packet⟩)
      let p := 10*Fintype.card (Wire Pair W)
      2^a ≤ 3*(live.image (colNode col)).card ∧ (∀ x ∈ live, nonpin col x) ∧
      (∀ x ∈ live, ∀ y ∈ live, ∀ addr : Fin f.natDegree → Bool, addr ≠ (fun _ => false) →
        ((physicalCell (balancedMask (a+1) b) (seat x)) i).1 =
          ((physicalCell (balancedMask (a+1) b) (seat y)) i).2 ∧
        (J6R9PacketLocal.W (a+1) (pow₂ (a+1) - 1)
          (((seat y).2.val:ℤ)-((seat x).2.val:ℤ))).eval₂
          (J6ZeroTransport.reduceAt p (scalar_nilpotent p f)) (probe p f addr) ≠ 0) := by
  obtain ⟨packet,hDense,hW⟩ := extreme_diagonal_10M_of_density (balancedMask (a+1) b) seat word hb _
    (diagonal_load_from_source_variance row col z seat seat_eq word dev he hdev hp hbig)
    f hf hd hprec i (colNode col) bounded

  refine ⟨packet,hDense,?_,hW⟩
  intro x hx
  rw [J7SeatCertificate.pin_nonpin_complement]
  intro hm
  obtain ⟨pin,_,rfl⟩ := Finset.mem_map.mp hm
  have hpage := (Finset.mem_filter.mp hx).2
  have hpair : seat (pinEmbed Pair W pin) =
      (⟨key (diagCell word),packet⟩,(seat (pinEmbed Pair W pin)).2) := Prod.ext hpage rfl
  have hcell : physicalCell (balancedMask (a+1) b) (seat (pinEmbed Pair W pin)) =
      diagCell word := by
    rw [hpair]
    exact diagonal_cell_uniform word (balancedMask (a+1) b) packet _
  have hneq := layout_owns_pins row col z hz pin
  rw [← seat_eq, hcell] at hneq
  exact hneq rfl

#print axioms extreme_diagonal_10M_from_source_certificate
end
end P6Joint
