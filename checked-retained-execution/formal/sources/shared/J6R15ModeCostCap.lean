import J6R15ModeCostSqrt

/-! Separates the per-node printed size parameters from the actual
metered exponent stream. This does not promise any cost for the
child constructors, tensor arithmetic, or complete recursion. -/
namespace J6R15ModeCost
open J6R10Repack

theorem parameter_product_bound (M D u p c : ℕ) (hu : 0<u)
    (hp : p*u≤c*M*D) : ((6*M)/D)*p≤(6*c*M*M)/u := by
  let B := (6*M)/D
  change B*p≤(6*c*M*M)/u
  have hB : B*D≤6*M := Nat.div_mul_le_self _ _
  apply (Nat.le_div_iff_mul_le hu).mpr
  calc
    (B*p)*u=B*(p*u) := by ring
    _≤B*(c*M*D) := Nat.mul_le_mul_left B hp
    _=(c*M)*(B*D) := by ring
    _≤(c*M)*(6*M) := Nat.mul_le_mul_left _ hB
    _=_ := by ring

theorem native_schedule_bound {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a p : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a)
    (ms : List (Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p))
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) (hp : 0<p) (hP : 6*Nat.card E≤p)
    (u c : ℕ) (hu : 0<u) (hcap : p*u≤c*Nat.card E*2^(a-i.val)) :
    (strictTuples (ms.map modeWeight) p).length≤
      2^(18*Nat.sqrt ((6*c*Nat.card E*Nat.card E)/u)) := by
  have H := parameter_product_bound (Nat.card E) (2^(a-i.val)) u p c hu hcap
  have hS := Nat.mul_le_mul_left 18 (Nat.sqrt_le_sqrt H)
  exact (native_sqrt_bound P i ms hm hall hp hP).trans
    (Nat.pow_le_pow_right (by decide) hS)

theorem native_paid_schedule_bound {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a p q : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a)
    (ms : List (Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p))
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) (hp : 0<p) (hP : 6*Nat.card E≤p)
    (u c : ℕ) (hu : 0<u) (hcap : p*u≤c*Nat.card E*2^(a-i.val))
    (hq : 0<q) (ws : List (Word q)) (prec : Word q)
    (hW : ws.map Word.val=ms.map modeWeight) (hpr : prec.val=p) :
    let xs := strictTuples (ms.map modeWeight) p
    ∃ S : State q, (start ws prec).result=.again S ∧ S.wellFormed ws.length ∧
      let run := collect ws.length (xs.length+1) S
      run.result.2=true ∧ run.result.1.map (List.map Word.val)=xs ∧
      (start ws prec).steps+run.steps≤16*q+14+4*(ws.length+1)*(q+1)+
        (2^(18*Nat.sqrt ((6*c*Nat.card E*Nat.card E)/u))+1)*delayCap q ws.length := by
  obtain ⟨S,hStart,hS,hEnd,hAll,hC⟩ := roster_paid hq hp ms ws prec hW hpr
  have H := native_schedule_bound P i ms hm hall hp hP u c hu hcap
  have HK := Nat.mul_le_mul_right (delayCap q ws.length) (Nat.succ_le_succ H)
  refine ⟨S,hStart,hS,hEnd,hAll,?_⟩
  exact hC.trans (Nat.add_le_add_left HK _)

#print axioms parameter_product_bound
#print axioms native_schedule_bound
#print axioms native_paid_schedule_bound
end J6R15ModeCost

