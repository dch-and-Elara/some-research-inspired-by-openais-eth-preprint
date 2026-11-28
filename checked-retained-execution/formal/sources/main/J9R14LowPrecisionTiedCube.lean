import J9R14LowPrecisionColumn

/-!
# Exact tied-bit reindexing, not an assumed independent sum

All protected original ports of one owner use a single common bit.
Pure equality tensors force exactly these coincidences. Other original
ports are kept as separate bits for their own (possibly coupled)
literal tables, rather than being assumed independent after weighting.
-/

namespace J9R14LowPrecisionTiedCube
open scoped Classical Polynomial BigOperators
open J9R14LowPrecisionColumn

noncomputable section
variable {Q U R : Type*} [Fintype Q] [Fintype U]

abbrev Rest (owner : Q→Option U) := {q : Q // owner q=none}

def Tied (owner : Q→Option U) (x : Q→Bool) : Prop :=
  ∀ u q q', owner q=some u → owner q'=some u → x q=x q'

def unlift (owner : Q→Option U) (x : Rest owner→Bool) (q : Q) : Bool :=
  if h : owner q=none then x ⟨q,h⟩ else false

def restrict (owner : Q→Option U) (x : Q→Bool) : Rest owner→Bool :=
  fun q => x q.val

omit [Fintype Q] [Fintype U] in
theorem encoded_tied (owner : Q→Option U) (x : Rest owner→Bool) (s : Finset U) :
    Tied owner (columnBits owner (unlift owner x) s) := by
  intro u q q' h h'
  simp [columnBits,h,h']

omit [Fintype Q] [Fintype U] in
theorem restriction_exact (owner : Q→Option U) (x : Rest owner→Bool) (s : Finset U) :
    restrict owner (columnBits owner (unlift owner x) s)=x := by
  funext q
  simp [restrict,columnBits,unlift,q.2]

def representative (owner : Q→Option U) (h : ∀ u, ∃ q, owner q=some u) (u : U) : Q :=
  Classical.choose (h u)

def decodeMask (owner : Q→Option U) (h : ∀ u, ∃ q, owner q=some u) (x : Q→Bool) : Finset U :=
  Finset.univ.filter (fun u => x (representative owner h u)=true)

def tiedEquiv (owner : Q→Option U) (h : ∀ u, ∃ q, owner q=some u) :
    ((Rest owner→Bool) × Finset U) ≃ {x : Q→Bool // Tied owner x} where
  toFun x := ⟨columnBits owner (unlift owner x.1) x.2, encoded_tied owner x.1 x.2⟩
  invFun x := (restrict owner x.1,decodeMask owner h x.1)
  left_inv x := by
    apply Prod.ext
    · exact restriction_exact owner x.1 x.2
    · ext u
      have hh := Classical.choose_spec (h u)
      change owner (representative owner h u)=some u at hh
      simp [decodeMask,columnBits,hh]
  right_inv x := by
    apply Subtype.ext
    funext q
    change columnBits owner (unlift owner (restrict owner x.1)) (decodeMask owner h x.1) q=x.1 q
    cases hq : owner q with
    | none => simp [columnBits,unlift,restrict,hq]
    | some u =>
      have hh := Classical.choose_spec (h u)
      change owner (representative owner h u)=some u at hh
      have he := x.2 u (representative owner h u) q hh hq
      simp [columnBits,hq,decodeMask,he]

variable [CommRing R]

/-- Literal product of protected equality gates: each gate can have
any positive arity (including one). -/
def guardWeight (owner : Q→Option U) (x : Q→Bool) : R :=
  ∏ u : U, if ∀ q q', owner q=some u → owner q'=some u → x q=x q'
    then 1 else 0

theorem guard_weight (owner : Q→Option U) (x : Q→Bool) :
    (guardWeight owner x : R) = if Tied owner x then 1 else 0 := by
  by_cases ht : Tied owner x
  · rw [if_pos ht]
    unfold guardWeight
    exact Finset.prod_eq_one (fun u _ => if_pos (ht u))
  · rw [if_neg ht]
    unfold Tied at ht
    push_neg at ht
    obtain ⟨u,q,q',hq,hq',hneq⟩ := ht
    have hbad : ¬∀ c c', owner c=some u → owner c'=some u → x c=x c' :=
      fun hh => hneq (hh q q' hq hq')
    unfold guardWeight
    exact Finset.prod_eq_zero (Finset.mem_univ u) (if_neg hbad)

theorem original_sum_tied (owner : Q→Option U) (h : ∀ u, ∃ q, owner q=some u)
    (restWeight : (Rest owner→Bool)→R) (f : (Q→Bool)→R) :
    (∑ x : Q→Bool, guardWeight owner x * restWeight (restrict owner x) * f x) =
      ∑ y : Rest owner→Bool, restWeight y *
        ∑ s : Finset U, f (columnBits owner (unlift owner y) s) := by
  simp only [guard_weight,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter]
  let s := (Finset.univ : Finset (Q→Bool)).filter (Tied owner)
  have hs (x : Q→Bool) : x∈s ↔ Tied owner x := by simp [s]
  let g (x : Q→Bool) := restWeight (restrict owner x)*f x
  change (∑ x∈s, g x)=_
  rw [Finset.sum_subtype s hs g]
  rw [← Equiv.sum_comp (tiedEquiv owner h) (fun x => g x.1),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  change restWeight (restrict owner (columnBits owner (unlift owner x) m)) *
    f (columnBits owner (unlift owner x) m) = _
  rw [restriction_exact]

#print axioms tiedEquiv
#print axioms guard_weight
#print axioms original_sum_tied

end
end J9R14LowPrecisionTiedCube
