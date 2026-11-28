import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite

/-! Appendix D, source lines 487--528.  A child edge is precisely one
retained *half-port* of the parent.  In particular a retained row bit and
a retained column bit of the same parent edge remain independent bits
in the child.  Both old sides are put on the new left; the right
endpoint is the packet owning the retained physical slot. -/
namespace J6R10Repack
open scoped BigOperators Classical

structure Network (E A B : Type*) where
  row : E → A
  col : E → B

abbrev Port (E : Type*) := E ⊕ E

variable {E A B K G : Type*}

def owner (N : Network E A B) : Port E → A ⊕ B
  | .inl e => .inl (N.row e)
  | .inr e => .inr (N.col e)

def edge : Port E → E := Sum.elim id id

def side : Port E → Bool
  | .inl _ => false
  | .inr _ => true

def retainedGroup (N : Network E A B) (group : A ⊕ B → G) (p : Port E) : G :=
  group (owner N p)

abbrev Old (group : A ⊕ B → G) (g : G) := {v : A ⊕ B // group v = g}

abbrev ChildEdge (N : Network E A B) (group : A ⊕ B → G) (g : G) :=
  {p : Port E // retainedGroup N group p = g}

def child (N : Network E A B) (group : A ⊕ B → G) (packet : E → K) (g : G) :
    Network (ChildEdge N group g) (Old group g) K where
  row p := ⟨owner N p.val,p.property⟩
  col p := packet (edge p.val)

/-- Same parent half-port supplies both adjacent child endpoints. -/
theorem child_endpoints (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (p : ChildEdge N group g) :
    ((child N group packet g).row p).val = owner N p.val ∧
    (child N group packet g).col p = packet (edge p.val) := ⟨rfl,rfl⟩

def childBits (N : Network E A B) (group : A ⊕ B → G) (g : G)
    (n : ℕ) (order : Fin n ≃ ChildEdge N group g) :
    (Fin n → Bool) ≃ (ChildEdge N group g → Bool) :=
  order.arrowCongr (Equiv.refl Bool)

theorem childBits_reads (N : Network E A B) (group : A ⊕ B → G)
    (g : G) (n : ℕ) (order : Fin n ≃ ChildEdge N group g)
    (x : Fin n → Bool) (p : ChildEdge N group g) :
    childBits N group g n order x p = x (order.symm p) := rfl

abbrev ParentPorts (N : Network E A B) (v : A ⊕ B) :=
  {p : Port E // owner N p = v}

/-- Old incidence is preserved even for a zero-degree vertex or a multiedge.
In particular the new graph cannot split a retained old tensor by packet. -/
def oldPortsEquiv (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (v : Old group g) :
    {p : ChildEdge N group g // (child N group packet g).row p = v}
      ≃ ParentPorts N v.val where
  toFun p := ⟨p.val.val,congrArg Subtype.val p.property⟩
  invFun p :=
    ⟨⟨p.val,(congrArg group p.property).trans v.property⟩,Subtype.ext p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem old_degree_exact (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (v : Old group g) :
    Nat.card {p : ChildEdge N group g // (child N group packet g).row p = v}
      = Nat.card (ParentPorts N v.val) :=
  Nat.card_congr (oldPortsEquiv N group packet g v)

def rowPortsEquiv (N : Network E A B) (a : A) :
    {e : E // N.row e = a} ≃ ParentPorts N (.inl a) where
  toFun p := ⟨.inl p.val,congrArg Sum.inl p.property⟩
  invFun
    | ⟨.inl p,h⟩ => ⟨p,Sum.inl.inj h⟩
    | ⟨.inr _,h⟩ => nomatch h
  left_inv _ := rfl
  right_inv
    | ⟨.inl _,_⟩ => rfl
    | ⟨.inr _,h⟩ => nomatch h

def colPortsEquiv (N : Network E A B) (b : B) :
    {e : E // N.col e = b} ≃ ParentPorts N (.inr b) where
  toFun p := ⟨.inr p.val,congrArg Sum.inr p.property⟩
  invFun
    | ⟨.inl _,h⟩ => nomatch h
    | ⟨.inr p,h⟩ => ⟨p,Sum.inr.inj h⟩
  left_inv _ := rfl
  right_inv
    | ⟨.inl _,h⟩ => nomatch h
    | ⟨.inr _,_⟩ => rfl

abbrev PacketPorts (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (k : K) :=
  {p : ChildEdge N group g // (child N group packet g).col p = k}

/-- Injectivity follows from physical same-slot row/column seating, with
the Bool side tag kept; dropping this tag would be false. -/
def packetPortsEmbedding {L : ℕ} (N : Network E A B)
    (group : A ⊕ B → G) (seat : E ↪ K × Fin L) (g : G) (k : K) :
    PacketPorts N group (fun e => (seat e).1) g k ↪ Fin L × Bool where
  toFun p := ((seat (edge p.val.val)).2,side p.val.val)
  inj' := by
    intro p q h
    have hslot := congrArg Prod.fst h
    have hside := congrArg Prod.snd h
    have hpage : (seat (edge p.val.val)).1 = (seat (edge q.val.val)).1 :=
      p.property.trans q.property.symm
    have hedge := seat.injective (Prod.ext hpage hslot)
    apply Subtype.ext
    apply Subtype.ext
    rcases p with ⟨⟨p,hp⟩,hpk⟩
    rcases q with ⟨⟨q,hq⟩,hqk⟩
    cases p <;> cases q <;> simp_all [side,edge]

theorem packet_degree_le {L : ℕ} (N : Network E A B)
    (group : A ⊕ B → G) (seat : E ↪ K × Fin L) (g : G) (k : K) :
    Nat.card (PacketPorts N group (fun e => (seat e).1) g k) ≤ 2*L := by
  have h := Nat.card_le_card_of_injective _ (packetPortsEmbedding N group seat g k).injective
  simpa [Nat.card_eq_fintype_card, mul_comm L 2] using h

abbrev rowsIn (N : Network E A B) (group : A ⊕ B → G) (g : G) :=
  {e : E // group (.inl (N.row e)) = g}

abbrev colsIn (N : Network E A B) (group : A ⊕ B → G) (g : G) :=
  {e : E // group (.inr (N.col e)) = g}

def splitSides (N : Network E A B) (group : A ⊕ B → G) (g : G) :
    ChildEdge N group g ≃ rowsIn N group g ⊕ colsIn N group g where
  toFun
    | ⟨.inl e,h⟩ => .inl ⟨e,h⟩
    | ⟨.inr e,h⟩ => .inr ⟨e,h⟩
  invFun
    | .inl ⟨e,h⟩ => ⟨.inl e,h⟩
    | .inr ⟨e,h⟩ => ⟨.inr e,h⟩
  left_inv
    | ⟨.inl _,_⟩ => rfl
    | ⟨.inr _,_⟩ => rfl
  right_inv
    | .inl _ => rfl
    | .inr _ => rfl

theorem child_edges_exact [Finite E] (N : Network E A B) (group : A ⊕ B → G)
    (g : G) :
    Nat.card (ChildEdge N group g) =
      Nat.card (rowsIn N group g) + Nat.card (colsIn N group g) := by
  rw [Nat.card_congr (splitSides N group g),Nat.card_sum]

def allPortsEquiv (N : Network E A B) (group : A ⊕ B → G) :
    (Σ g : G, ChildEdge N group g) ≃ Port E where
  toFun p := p.2.val
  invFun p := ⟨retainedGroup N group p,p,rfl⟩
  left_inv := by
    rintro ⟨g,p,hp⟩
    subst g
    rfl
  right_inv _ := rfl

theorem all_children_conserve_ports [Fintype E] [Fintype G] (N : Network E A B)
    (group : A ⊕ B → G) :
    (∑ g : G, Nat.card (ChildEdge N group g)) = 2 * Nat.card E := by
  letI (g : G) : Fintype (ChildEdge N group g) :=
    Fintype.ofFinite _
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma, Fintype.card_congr (allPortsEquiv N group), Fintype.card_sum,two_mul]

/-- The exact side marginals of Lemma D.2 imply its printed child bound.
M may be supplied from the current valid call (and need not be re-counted). -/
theorem printed_child_shrink [Finite E] (N : Network E A B) (group : A ⊕ B → G)
    (g : G) (M : ℕ) (hM : 0 < M)
    (hr : Nat.card (rowsIn N group g) ≤ 3*M/64)
    (hc : Nat.card (colsIn N group g) ≤ 3*M/64) :
    32 * Nat.card (ChildEdge N group g) ≤ 3*M ∧
    8 * Nat.card (ChildEdge N group g) ≤ M ∧ Nat.card (ChildEdge N group g) < M := by
  rw [child_edges_exact]
  omega

/-- Degree invariant of the actual child network: all retained old degrees
are unchanged and a new packet receives at most two ports per packet slot. -/
theorem printed_child_degrees {L Δ : ℕ} (N : Network E A B) (group : A ⊕ B → G)
    (seat : E ↪ K × Fin L) (g : G)
    (hr : ∀ a, Nat.card {e : E // N.row e = a} ≤ Δ)
    (hc : ∀ b, Nat.card {e : E // N.col e = b} ≤ Δ)
    (hL : 2*L ≤ Δ) :
    (∀ v : Old group g,
      Nat.card {p : ChildEdge N group g // (child N group (fun e => (seat e).1) g).row p = v}
        ≤ Δ) ∧
    (∀ k : K, Nat.card (PacketPorts N group (fun e => (seat e).1) g k) ≤ Δ) := by
  constructor
  · intro v
    rw [old_degree_exact]
    rcases v with ⟨a|b,h⟩
    · rw [← Nat.card_congr (rowPortsEquiv N a)]
      exact hr a
    · rw [← Nat.card_congr (colPortsEquiv N b)]
      exact hc b
  · intro k
    exact (packet_degree_le N group seat g k).trans hL

#print axioms child_endpoints
#print axioms childBits_reads
#print axioms old_degree_exact
#print axioms packet_degree_le
#print axioms child_edges_exact
#print axioms all_children_conserve_ports
#print axioms printed_child_shrink
#print axioms printed_child_degrees
end J6R10Repack
