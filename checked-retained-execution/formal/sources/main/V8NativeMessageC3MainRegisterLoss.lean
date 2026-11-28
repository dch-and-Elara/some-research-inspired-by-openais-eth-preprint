import V8NativeMessageC3MainDenominator

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! The exact source MAIN denominator to the whole product degree,
not charged once per group. All fixed weights may be dyadically
integral jets (integer-coefficient weights are a special case). -/
namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive V8PooledRange
noncomputable section

def localJetHom (k : ℕ) : TwoLocal[X] →+* C3.Jet ℚ k :=
  (AdjoinRoot.mk ((X:ℚ[X])^k)).comp (mapRingHom twoLocalRat)

def localJetImage (k : ℕ) : Subring (C3.Jet ℚ k) :=
  (localJetHom k).range

theorem integer_to_local_jet (k : ℕ) {q : ℚ[X]} (hq : q∈intPolynomialImage) :
    AdjoinRoot.mk ((X:ℚ[X])^k) q ∈ localJetImage k := by
  obtain ⟨r,rfl⟩ := hq
  refine ⟨r.map (Int.castRingHom TwoLocal),?_⟩
  change AdjoinRoot.mk ((X:ℚ[X])^k)
    ((r.map (Int.castRingHom TwoLocal)).map twoLocalRat) =
      AdjoinRoot.mk ((X:ℚ[X])^k) (r.map (Int.castRingHom ℚ))
  rw [map_integer_poly]

theorem delta_jet_mem (n k : ℕ) : (n:C3.Jet ℚ k)∈localJetImage k := by
  exact ⟨(n:TwoLocal[X]),map_natCast (localJetHom k) n⟩

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ] {G : Graph V E} {p : ThreePorts G}
variable (F : FiveFile (Γ:=Γ) G p) (a : Address F.layout) (k : ℕ)

theorem local_theta (g : Γ) (x : Fibre F.layout a g) (c : ClauseId V E)
    (v : Variable V) (hv : v∈F.layout.scope c) :
    ((δ F.layout:C3.Jet ℚ k)*theta F.layout a g x k c v)∈localJetImage k := by
  have h := integer_to_local_jet k (actual_theta_denominator F.layout a g x c v hv)
  rw [map_mul,C_eq_natCast,map_natCast] at h
  exact h

private theorem scaled_false_lit {R : Type*} [CommRing R] (I : Subring R) {d x : R}
    (hd : d∈I) (hx : d*x∈I) (s : Bool) : d*(1-literal s x)∈I := by
  cases s
  · simpa [literal] using hx
  · rw [show d*(1-literal true x)=d-d*x by simp [literal,mul_sub]]
    exact I.sub_mem hd hx

theorem local_clause (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) (c : ClauseId V E) :
    ((δ F.layout:C3.Jet ℚ k)^2*clauseJet F a k s g x c)∈localJetImage k := by
  let d : C3.Jet ℚ k := δ F.layout
  let cc := clauses G p s c
  let u := theta F.layout a g x k c cc.1.1
  let v := theta F.layout a g x k c cc.2.1
  let I := localJetImage k
  have hscope := true_ports_in_scope F s c
  have hd : d∈I := delta_jet_mem _ _
  have hu : d*u∈I := local_theta F a k g x c _ hscope.1
  have hv : d*v∈I := local_theta F a k g x c _ hscope.2
  change d^2*(1-(1-literal cc.1.2 u)*(1-literal cc.2.2 v))∈I
  rw [show d^2*(1-(1-literal cc.1.2 u)*(1-literal cc.2.2 v)) =
    d^2 - (d*(1-literal cc.1.2 u))*(d*(1-literal cc.2.2 v)) by ring]
  exact I.sub_mem (I.pow_mem hd 2)
    (I.mul_mem (scaled_false_lit I hd hu _) (scaled_false_lit I hd hv _))

def ownedClauses (g : Γ) : Finset (ClauseId V E) :=
  Finset.univ.filter (fun c => F.layout.factorGroup a.t c=g)

theorem ownership_count :
    (∑ g, (ownedClauses F a g).card) = Fintype.card (ClauseId V E) := by
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv (fun c : ClauseId V E => F.layout.factorGroup a.t c))
  rw [Fintype.card_sigma] at he
  have hc (g : Γ) : Fintype.card {c : ClauseId V E // F.layout.factorGroup a.t c=g} =
      (ownedClauses F a g).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun c => by simp [ownedClauses])
  simpa only [hc] using he

theorem local_point (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) :
    ((δ F.layout:C3.Jet ℚ k)^(2*(ownedClauses F a g).card)*actualPoint F a k s g x)∈localJetImage k := by
  let d : C3.Jet ℚ k := δ F.layout
  have hP : actualPoint F a k s g x=∏ c∈ownedClauses F a g, clauseJet F a k s g x c := by
    rw [ownedClauses,Finset.prod_filter]
    rfl
  have he : ((∏ c∈ownedClauses F a g, d^2*clauseJet F a k s g x c) : C3.Jet ℚ k) =
      d^(2*(ownedClauses F a g).card)*actualPoint F a k s g x := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,← pow_mul,hP]
  change d^(2*(ownedClauses F a g).card)*actualPoint F a k s g x∈localJetImage k
  rw [← he]
  exact (localJetImage k).prod_mem (fun c _ => local_clause F a k s g x c)

theorem local_register {b : Γ→ℕ} (Q : NativePrivateLists F a k b)
    (hw : ∀ g j, Q.weight g j ∈localJetImage k) (s : V→Bool) :
    ((δ F.layout:C3.Jet ℚ k)^(2*Fintype.card (ClauseId V E)) * actualRegister F a k Q s)∈
      localJetImage k := by
  let d : C3.Jet ℚ k := δ F.layout
  have he : (∑ g, 2*(ownedClauses F a g).card) = 2*Fintype.card (ClauseId V E) := by
    rw [← Finset.mul_sum,ownership_count F a]
  have fact :
      (∏ g, d^(2*(ownedClauses F a g).card) *
        ∑ j : Fin (b g), Q.weight g j*actualPoint F a k s g (Q.point g j)) =
      d^(2*Fintype.card (ClauseId V E))*actualRegister F a k Q s := by
    rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,he]
    rfl
  change d^(2*Fintype.card (ClauseId V E))*actualRegister F a k Q s∈localJetImage k
  rw [← fact]
  refine (localJetImage k).prod_mem (fun g _ => ?_)
  rw [Finset.mul_sum]
  refine (localJetImage k).sum_mem (fun j _ => ?_)
  rw [show d^(2*(ownedClauses F a g).card) * (Q.weight g j * actualPoint F a k s g (Q.point g j)) =
      Q.weight g j * (d^(2*(ownedClauses F a g).card) * actualPoint F a k s g (Q.point g j)) by ring]
  exact (localJetImage k).mul_mem (hw g j) (local_point F a k s g (Q.point g j))

#print axioms integer_to_local_jet
#print axioms local_theta
#print axioms local_clause
#print axioms ownership_count
#print axioms local_point
#print axioms local_register
end
end V8NativeMessage.C3.RawMain