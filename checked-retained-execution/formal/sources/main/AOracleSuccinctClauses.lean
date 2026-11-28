import AOracleSuccinct

/-!
# Literal CNF clauses and equality vertices for A1

The original table values need not even be supplied for these
constraints: evaluate the signed clause or equality on its incident
ports. The bounded table realization is given with exact indexing.
-/

namespace AOracleSuccinctClauses
open AOracleSuccinct

def unpackBits : (d : ℕ) → ℕ → Fin d → Bool
  | 0, _, i => Fin.elim0 i
  | d+1, n, i => Fin.cases (decide (n%2=1)) (unpackBits d (n/2)) i

theorem unpack_rank {d : ℕ} (a : Fin d → Bool) :
    unpackBits d (rankBits a) = a := by
  induction d with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ d ih =>
    funext i
    let tail := fun j : Fin d => a j.succ
    have h : rankBits a = (a 0).toNat + 2*rankBits tail := rfl
    have hb : (a 0).toNat ≤ 1 := by cases a 0 <;> decide
    have hdiv : rankBits a / 2 = rankBits tail := by omega
    have hmod : rankBits a % 2 = (a 0).toNat := by omega
    refine Fin.cases ?_ (fun j => ?_) i
    · change decide (rankBits a%2=1)=a 0
      rw [hmod]
      cases a 0 <;> decide
    · change unpackBits d (rankBits a/2) j = a j.succ
      rw [hdiv]
      exact congrFun (ih tail) j

/-- The truth table is indexed by input bits, not by signed truth,
so its stored index agrees with the source incidence list. -/
def realize {n d delta : ℕ} (hd : d ≤ delta) (port : Fin d → Fin n)
    (gate : (Fin d → Bool) → Bool) : BoolTensor n delta :=
  ⟨d,hd,port,fun k => gate (unpackBits d k.val)⟩

theorem realize_read {n d delta : ℕ} (hd : d ≤ delta) (port : Fin d → Fin n)
    (gate : (Fin d → Bool) → Bool) (a : Fin n → Bool) :
    (realize hd port gate).read a = gate (fun j => a (port j)) := by
  simp only [BoolTensor.read, realize, unpack_rank]

/-- The empty OR is false, and repeated original occurrences are
accepted without any deduplication assumption. -/
def clause {d : ℕ} (positive : Fin d → Bool) (a : Fin d → Bool) : Bool :=
  decide (∃ j, a j = positive j)

def equalVertex {d : ℕ} (a : Fin d → Bool) : Bool :=
  decide (∀ j k, a j = a k)

theorem signed_clause_entry {n d delta : ℕ} (hd : d ≤ delta)
    (port : Fin d → Fin n) (sign : Fin d → Bool) (a : Fin n → Bool) :
    (realize hd port (clause sign)).read a = true ↔
      ∃ j, a (port j) = sign j := by
  rw [realize_read, clause, decide_eq_true_eq]

theorem equality_vertex_entry {n d delta : ℕ} (hd : d ≤ delta)
    (port : Fin d → Fin n) (a : Fin n → Bool) :
    (realize hd port equalVertex).read a = true ↔ ∀ j k, a (port j) = a (port k) := by
  rw [realize_read, equalVertex, decide_eq_true_eq]

#print axioms unpack_rank
#print axioms realize_read
#print axioms signed_clause_entry
#print axioms equality_vertex_entry

end AOracleSuccinctClauses

