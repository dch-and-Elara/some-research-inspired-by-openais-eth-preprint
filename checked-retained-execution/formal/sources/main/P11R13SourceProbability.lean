import P11R13PrintedPadding

namespace P11R13SourceProbability
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11R12Probability P11R12Variance J1PPrinted
open OuterNodePacking P11R13PrintedPadding
variable {K E : Type*} [LinearOrder K] [Fintype K] [Fintype E]
  [Nonempty E] [DecidableEq E] {n : ℕ}

/-- Original implicit Hpad and D_arr are obtained from the same genuine
ordered cell loads. Only the original input degree/size and selected
cell-collision/common-column assumptions are required. -/
theorem all_shifts_printed_padding (s d : ℕ) (hK : Fintype.card K=64)
    (e : Fin n ≃ Key (Fin (stepA (Nat.clog 2 s) d)) K)
    (f : E×Bool → Cell (Fin (stepA (Nat.clog 2 s) d)) K)
    (column : ∀ v i, (f (v,false) i).2 = (f (v,true) i).2)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hActive : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < Fintype.card (E×Bool))
    (hColl : PaddingBounds.collision Finset.univ (load f) (Fintype.card (E×Bool)) ≤
      2*(Fintype.card (E×Bool):ℝ)*sourceDelta s)
    (packets : Finset (Page (stepA (Nat.clog 2 s) d) (printedB f) K))
    (nodes : Finset ℤ) :
    let L : ℚ := ((2:ℕ)^stepA (Nat.clog 2 s) d:ℚ)
    let A : ℚ := (Fintype.card E:ℚ)/L^2
    1-128/L^5 ≤ RandomEndpoint.probability (PacketVariance.product (sampleWeight (printedB f) e))
      (fun x => ∀ t∈nodes, t≠0 →
        (1-1/((printedB f):ℚ)-1/L^2)*A ≤
          ((untouched Finset.univ (vertexOwner (seat (toDraw e x) f (cap_of_printedB f)))
            (matchedColumns packets (realSlot (seat (toDraw e x) f (cap_of_printedB f)))
              (realSlot (seat (toDraw e x) f (cap_of_printedB f))) t)).card:ℚ)) := by
  classical
  obtain ⟨_,hb,hH,hSlots⟩ := physical_guards s d hK f hU hActive hColl
  have hCard : Fintype.card (E×Bool)=2*Fintype.card E := by
    rw [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm]
  rw [hCard] at hSlots
  exact printed_P11 e f (cap_of_printedB f) column hb hH hK hSlots packets nodes

#print axioms all_shifts_printed_padding
end P11R13SourceProbability
