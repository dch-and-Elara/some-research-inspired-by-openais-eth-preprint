import J1R15Pipeline

/-! Finite MAIN register comparison. The target is the fixed-width biased
address word, not a precomputed yes/no result. The same equality scan that
checks indices now compares the two accumulator tapes. -/
namespace J1R15
open AOracleMachineTime AOracleMachineTimeTape A1R10 J1R14Query J1MainSourcePlacement MainProbe

theorem bitsValue_inj_sameLength (x y : List Bool) (hlen : x.length=y.length)
    (he : bitsValue x=bitsValue y) : x=y := by
  induction x generalizing y with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a x ih =>
    cases y with
    | nil => simp at hlen
    | cons b y =>
      rw [bitsValue,bitsValue] at he
      have ha : a.toNat ≤ 1 := by cases a <;> decide
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      have h : a.toNat=b.toNat := by omega
      have hhead : a=b := by cases a <;> cases b <;> simp_all
      subst b
      exact congrArg (List.cons a) (ih y (by simpa only [List.length_cons,Nat.succ.injEq] using hlen)
        (by omega))

theorem wordRead_inj (p : ℕ) : Function.Injective (@wordRead p) := by
  intro a b he
  have ha : (wordRead a).val = bitsValue a.val := ZMod.val_natCast_of_lt
    (by simpa only [a.property] using bitsValue_lt a.val)
  have hb : (wordRead b).val = bitsValue b.val := ZMod.val_natCast_of_lt
    (by simpa only [b.property] using bitsValue_lt b.val)
  apply Subtype.ext
  exact bitsValue_inj_sameLength _ _ (a.property.trans b.property.symm)
    (ha.symm.trans ((congrArg ZMod.val he).trans hb))

def compareWord {p : ℕ} (m : Meter (Word p)) (goal : Word p) : Meter Bool :=
  let cmp := equalBits m.result.val goal.val
  ⟨cmp.result,m.steps+cmp.steps⟩

theorem compareWord_result {p : ℕ} (m : Meter (Word p)) (goal : Word p) :
    (compareWord m goal).result = decide (wordRead m.result=wordRead goal) := by
  rw [compareWord,equalBits_result,decide_eq_decide]
  exact ⟨fun h => congrArg wordRead (Subtype.ext h),fun h =>
    congrArg Subtype.val (wordRead_inj p h)⟩

theorem compareWord_cost {p : ℕ} (m : Meter (Word p)) (goal : Word p) :
    (compareWord m goal).steps = m.steps+4*p+1 := by
  simp [compareWord,equalBits_cost,m.result.property,goal.property,Nat.add_assoc]

/-- Representation of an already specified input number, separate from the
tape running cost. The signed row is accumulated from the public bias D and
compared directly with the y-register. -/
def natWord (p k : ℕ) : Word p := ⟨encodeBits p k,encodeBits_length p k⟩

theorem natWord_read (p k : ℕ) (hk : k<2^p) :
    wordRead (natWord p k)=(k:ZMod (2^p)) := by
  change (bitsValue (encodeBits p k):ZMod (2^p))=_
  rw [encodeBits_exact p k hk]

theorem biasedTarget {D p : ℕ} (y : Box D) :
    (y.val : ZMod (2^p)) = (D : ZMod (2^p)) + (boxValue y : ZMod (2^p)) := by
  simp only [boxValue,Int.cast_sub,Int.cast_natCast]
  ring

section Source
variable {q r n M h d p : ℕ} {E F A : Type*} [Fintype E]
variable (data : IncidenceData (Fin q) (Fin r) E (Fin n) F)
variable (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
variable (order : Fin M ≃ E)
variable (pin : A → E) (diag : ∀ a, (data.cell (pin a)).1 = (data.cell (pin a)).2)
variable (interval : Finset ℕ) (hz : 0 ∉ interval)

local notation "D₀" => Fintype.card (Cell (Fin q) (Fin r))
local notation "L₀" => sourceLayout data h cap pin diag

noncomputable def sourceRowTest (hp : 0<p) (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (b : Exceptional (Fin q) (Fin r) interval)
    (e : Fin d ≃ Cell (Fin q) (Fin r)) (y : Box D₀) : Meter Bool :=
  compareWord (sourceExecution data cap order hp (natWord p D₀) x t g c b.val e)
    (natWord p y.val)

theorem sourceRowTest_exact (hp : 0<p) (hwide : 2*D₀ < 2^p)
    (x : Fin n → Bool) (t : Fin q) (g : Fin r) (c : Fin h)
    (b : Exceptional (Fin q) (Fin r) interval) (e : Fin d ≃ Cell (Fin q) (Fin r)) (y : Box D₀) :
    (sourceRowTest data cap order interval hp x t g c b e y).result =
      decide (rowRead L₀ (printedBasis L₀ interval hz) t g (c,b) x = boxValue y) := by
  have hD : D₀ < 2^p := by omega
  have hy : y.val < 2^p := by
    have hy := y.isLt
    omega
  rw [sourceRowTest,compareWord_result,sourceExecution_exact data cap order pin diag interval hz,
    natWord_read p _ hD,natWord_read p _ hy,biasedTarget y,decide_eq_decide]
  refine (add_right_inj _).trans ?_
  exact signed_cast_equal_iff hwide _ _
    (printed_read_bounds L₀ interval hz t g (c,b) x) (boxValue_bounds y)

theorem sourceRowTest_cost (hp : 0<p) (x : Fin n → Bool) (t : Fin q) (g : Fin r) (c : Fin h)
    (b : Exceptional (Fin q) (Fin r) interval) (e : Fin d ≃ Cell (Fin q) (Fin r)) (y : Box D₀) :
    (sourceRowTest data cap order interval hp x t g c b e y).steps ≤
      (n*(2*Nat.clog 2 n+3)+1) + (d*(slotBudget q r n M h+1)+1) +
        d*(2+32*(p+1)^2) + 4*p + 1 := by
  rw [sourceRowTest,compareWord_cost]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (sourceExecution_cost data cap order interval hp (natWord p D₀) x t g c b e) _) _
end Source

#print axioms bitsValue_inj_sameLength
#print axioms wordRead_inj
#print axioms compareWord_result
#print axioms compareWord_cost
#print axioms natWord_read
#print axioms biasedTarget
#print axioms sourceRowTest_exact
#print axioms sourceRowTest_cost
end J1R15
