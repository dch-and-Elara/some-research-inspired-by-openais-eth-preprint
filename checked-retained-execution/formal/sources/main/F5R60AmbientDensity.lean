import F5R60AmbientDegree
import F5R60AmbientRequests
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Original F5 counts on the same real endpoint graph, not arithmetic
about unrelated supplied counts. In the decision branch each triple
uses three disjoint original occurrence seats on the old half. -/
namespace F5R60.Ambient
set_option autoImplicit false
open scoped Classical BigOperators
noncomputable section

variable {n : ℕ}

def forwardEdgeEquiv (G : SimpleGraph (Fin n)) : ForwardEdge G ≃ G.edgeSet := by
  let encode (e : ForwardEdge G) : G.edgeSet :=
    ⟨s(e.val.1,e.val.2),e.property.2⟩
  refine Equiv.ofBijective encode ⟨?_,?_⟩
  · intro a b eq
    have qu : s(a.val.1,a.val.2)=s(b.val.1,b.val.2) := congrArg Subtype.val eq
    rcases Sym2.eq_iff.mp qu with ⟨l,r⟩ | ⟨l,r⟩
    · exact Subtype.ext (Prod.ext l r)
    · exfalso
      have h := a.property.1
      rw [l,r] at h
      exact (not_lt_of_ge h.le) b.property.1
  · rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      have h : G.Adj a b := he
      let d := orient G h
      refine ⟨d,Subtype.ext ?_⟩
      change s(d.val.1,d.val.2)=s(a,b)
      rcases orient_endpoints G h with hp | hp
      · rw [show d.val=(a,b) from hp]
      · rw [show d.val=(b,a) from hp]
        exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)

def actual_joined_edge_equiv (H B : SimpleGraph (Fin n)) :
    Edge H B ≃ (joined H B).edgeSet := by
  let code (e : Edge H B) : (joined H B).edgeSet :=
    ⟨s(ends H B e false,ends H B e true),actual_edges_are_joined H B e⟩
  refine Equiv.ofBijective code ⟨?_,?_⟩
  · intro a b eq
    have raw : s(ends H B a false,ends H B a true)=s(ends H B b false,ends H B b true) :=
      congrArg Subtype.val eq
    exact unordered_joined_edge_unique H B _ _ (Sym2.eq_iff.mp raw)
  · rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨d,hd⟩ := (joined_adj_iff_tagged_edge H B a b).1 he
      exact ⟨d,Subtype.ext (Sym2.eq_iff.mpr hd)⟩

theorem forward_handshaking (G : SimpleGraph (Fin n)) :
    2*Nat.card (ForwardEdge G) = ∑ i : Fin n, Nat.card (Neighbor G i) := by
  letI : DecidableRel G.Adj := fun a b => Classical.propDecidable (G.Adj a b)
  calc
    2*Nat.card (ForwardEdge G) = 2*(G.edgeFinset).card := by
      rw [Nat.card_congr (forwardEdgeEquiv G),Nat.card_eq_fintype_card,G.edgeFinset_card]
    _ = ∑ i : Fin n, G.degree i := G.sum_degrees_eq_twice_card_edges.symm
    _ = _ := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hc : Nat.card (Neighbor G i) = Fintype.card (G.neighborSet i) := by
        change Nat.card (G.neighborSet i)=Fintype.card (G.neighborSet i)
        exact Nat.card_eq_fintype_card
      exact (hc.trans (G.card_neighborSet_eq_degree i)).symm

theorem old_edge_count_at_most_two_n (H : SimpleGraph (Fin n))
    (degreeFour : ∀ i, Nat.card (Neighbor H i)≤4) :
    Nat.card (ForwardEdge H)≤2*n := by
  have hsum : (∑ i : Fin n, Nat.card (Neighbor H i)) ≤ ∑ _i : Fin n, 4 :=
    Finset.sum_le_sum (fun i _ => degreeFour i)
  have hc : (∑ _i : Fin n, (4:ℕ))=4*n := by simp [Nat.mul_comm]
  have he : 2*Nat.card (ForwardEdge H)≤4*n :=
    (forward_handshaking H).trans_le (hsum.trans hc.le)
  omega

theorem actual_cubic_backbone_edge_count (B : SimpleGraph (Fin n))
    (cubic : ∀ i, Nat.card (Neighbor B i)=3) :
    2*Nat.card (ForwardEdge B)=3*n := by
  calc
    2*Nat.card (ForwardEdge B) = ∑ i : Fin n, Nat.card (Neighbor B i) := forward_handshaking B
    _ = ∑ _i : Fin n, (3:ℕ) := Finset.sum_congr rfl (fun i _ => cubic i)
    _ = 3*n := by simp [Nat.mul_comm]

variable {C V : Type}
variable (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)

include key in
theorem actual_disjoint_triples_density [Finite C] : 3*Nat.card (TripleClause S)≤n := by
  let index (u : TripleClause S × Fin 3) : Fin n :=
    key (F5R59.atThree S u.1.val u.1.property u.2)
  have h : Function.Injective index := by
    intro a b h
    have hSame := key.injective h
    apply Prod.ext
    · exact Subtype.ext (congrArg Sigma.fst hSame)
    · exact Fin.ext (congrArg (fun x : F5R59.Vertex S => x.snd.val) hSame)
  have hc := Nat.card_le_card_of_injective index h
  simpa only [Nat.card_prod,Nat.card_fin,Nat.mul_comm] using hc

theorem original_decision_ambient_density [Finite C] (B : SimpleGraph (Fin n))
    (width : ∀ c, S.width c≤3) (occ : ∀ v, Nat.card (VariableSlots S v)≤3)
    (cubic : ∀ i, Nat.card (Neighbor B i)=3) :
    4*Nat.card (Edge (paddedH S key) B)≤9*Nat.card (Vertices n) ∧
      6*Nat.card (TripleClause S)≤Nat.card (Vertices n) := by
  have hc : Nat.card (Vertices n)=2*n := by rw [Nat.card_eq_fintype_card,joined_vertices_card]
  have ho := old_edge_count_at_most_two_n (paddedH S key)
    (actual_padded_degree_at_most_four S key width occ)
  have hb := actual_cubic_backbone_edge_count B cubic
  have hT := actual_disjoint_triples_density S key
  simp only [Edge,Nat.card_sum,Nat.card_fin,hc]
  omega

theorem original_F2_main_density [Finite C] (B : SimpleGraph (Fin n))
    (width : ∀ c, S.width c≤3) (occ : ∀ v, Nat.card (VariableSlots S v)≤3)
    (cubic : ∀ i, Nat.card (Neighbor B i)=3) :
    let N := Nat.card (Vertices n)
    let E := Nat.card (Edge (paddedH S key) B)
    let T := Nat.card (TripleClause S)
    let M := 3*(2*N+5*E+10*T)+2
    4*M≤179*N+8 ∧ (8<N → M<45*N) := by
  dsimp only
  obtain ⟨e,t⟩ := original_decision_ambient_density S key B width occ cubic
  omega

def evenPaddedSize (m : ℕ) : ℕ := m+m%2

theorem even_padding_guards (m : ℕ) :
    Even (evenPaddedSize m) ∧ m≤evenPaddedSize m ∧ evenPaddedSize m≤m+1 := by
  refine ⟨⟨m/2+m%2,?_⟩,?_,?_⟩ <;> unfold evenPaddedSize <;> omega

theorem finite_even_padded_key [Finite C] :
    Nonempty (F5R59.Vertex S ↪ Fin (evenPaddedSize (Nat.card (F5R59.Vertex S)))) := by
  letI : Fintype (F5R59.Vertex S) := Fintype.ofFinite _
  let eq := Fintype.equivFin (F5R59.Vertex S)
  have hCard : Fintype.card (F5R59.Vertex S)=Nat.card (F5R59.Vertex S) :=
    Nat.card_eq_fintype_card.symm
  exact ⟨eq.toEmbedding.trans (Fin.castLEEmb (hCard.trans_le (even_padding_guards _).2.1))⟩

#print axioms forwardEdgeEquiv
#print axioms actual_joined_edge_equiv
#print axioms forward_handshaking
#print axioms old_edge_count_at_most_two_n
#print axioms actual_cubic_backbone_edge_count
#print axioms actual_disjoint_triples_density
#print axioms original_decision_ambient_density
#print axioms original_F2_main_density
#print axioms even_padding_guards
#print axioms finite_even_padded_key
end
end F5R60.Ambient
