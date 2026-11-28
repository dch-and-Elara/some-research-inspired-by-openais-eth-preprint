import V8NativeMessageN6DTarget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5200000

/-! Exterior matching locality and exact support, independent of
the arithmetic used to evaluate an individual listed source term. -/
namespace V8NativeMessage.N6D
open scoped Classical BigOperators
open Paper5.HybridClosure
noncomputable section

variable {V G : Type} [DecidableEq V] [Fintype G] [DecidableEq G]
variable (E : Finset (V×V)) (cubic : ∀ v, GraphCutMoments.degree E v=3)
variable (owner : TriVertex V→G)
variable {R : Type*} [CommSemiring R] [Nontrivial R]

def UsesOnly (value : G→(TriVertex V→Bool)→R) : Prop :=
  ∀ g σ τ, (∀ v, owner v=g → σ v=τ v) → value g σ=value g τ

/-- The all-true boundary on the original exterior pair gives the
actual two-by-two OR obstruction, also over an arbitrary nontrivial
commutative semiring. The source uses its characteristic-two field. -/
theorem exterior_pair_same_group (value : G→(TriVertex V→Bool)→R)
    (scope : UsesOnly owner value)
    (correct : ∀ σ, (∏ g, value g σ)=UD E cubic R σ) (e : E) :
    owner (seat E cubic e false)=owner (seat E cubic e true) := by
  by_contra ne
  let g := owner (seat E cubic e false)
  let A (x : Bool) := value g (pairWord E cubic e x true)
  let B (y : Bool) := ∏ j ∈ Finset.univ.erase g, value j (pairWord E cubic e true y)
  have eq (x y : Bool) : A x*B y=orValue R x y := by
    calc
      _ = value g (pairWord E cubic e x y) *
          ∏ j ∈ Finset.univ.erase g, value j (pairWord E cubic e x y) := by
        apply congrArg₂ (· * ·)
        · symm
          apply scope g
          intro v hv
          apply pairWord_left_only E cubic e x y v
          intro h
          exact ne (hv.symm.trans (congrArg owner h))
        · apply Finset.prod_congr rfl
          intro j hj
          symm
          apply scope j
          intro v hv
          apply pairWord_right_only E cubic e x y v
          intro h
          exact (Finset.mem_erase.mp hj).1 (hv.symm.trans (congrArg owner h))
      _ = ∏ j, value j (pairWord E cubic e x y) := Finset.mul_prod_erase Finset.univ (fun j : G => value j (pairWord E cubic e x y)) (Finset.mem_univ g)
      _ = UD E cubic R (pairWord E cubic e x y) := correct _
      _ = _ := UD_one_pair E cubic R e x y
  have h00 : A false*B false=0 := by simpa [orValue] using eq false false
  have h10 : A true*B false=1 := by simpa [orValue] using eq true false
  have h01 : A false*B true=1 := by simpa [orValue] using eq false true
  have hz : (1:R)=0 := by
    calc
      _ = (A false*B true)*(A true*B false) := by rw [h01,h10,one_mul]
      _ = (A false*B false)*(A true*B true) := by ac_rfl
      _ = _ := by rw [h00,zero_mul]
  exact one_ne_zero hz

abbrev LocalPairs (g : G) := {e : E // owner (seat E cubic e false)=g}

abbrev AllowedPair := {u : Bool×Bool // (u.1||u.2)=true}

theorem allowedPairs : Fintype.card AllowedPair=3 := by decide

def localWord (g : G) (x : LocalPairs E cubic owner g→AllowedPair) : TriVertex V→Bool :=
  pairsWord E cubic (fun e => if h : owner (seat E cubic e false)=g then
    (x ⟨e,h⟩).val else (true,true))

omit [Fintype G] in
theorem localWord_on (g : G) (x : LocalPairs E cubic owner g→AllowedPair)
    (e : LocalPairs E cubic owner g) (b : Bool) :
    localWord E cubic owner g x (seat E cubic e.val b) =
      if b then (x e).val.2 else (x e).val.1 := by
  simp only [localWord,pairsWord_on,dif_pos e.property]

omit [Fintype G] [Nontrivial R] in
theorem UD_localWord (g : G) (x : LocalPairs E cubic owner g→AllowedPair) :
    UD E cubic R (localWord E cubic owner g x)=1 := by
  apply Finset.prod_eq_one
  intro e _
  by_cases h : owner (seat E cubic e false)=g
  · let e' : LocalPairs E cubic owner g := ⟨e,h⟩
    rw [localWord_on E cubic owner g x e' false,localWord_on E cubic owner g x e' true]
    simp [orValue,(x e').property]
  · simp [localWord,pairsWord_on,h,orValue]

omit [Fintype G] in
theorem localWords_injective (mono : ∀ e : E,
    owner (seat E cubic e false)=owner (seat E cubic e true)) (g : G) :
    Function.Injective (fun x : LocalPairs E cubic owner g→AllowedPair =>
      fun v : {v : TriVertex V // owner v=g} => localWord E cubic owner g x v.val) := by
  intro x y same
  funext e
  apply Subtype.ext
  apply Prod.ext
  · let v : {v : TriVertex V // owner v=g} := ⟨seat E cubic e.val false,e.property⟩
    simpa only [v,localWord_on E cubic owner g _ e false,ite_false,Bool.false_eq_true] using congrFun same v
  · let v : {v : TriVertex V // owner v=g} := ⟨seat E cubic e.val true,(mono e.val).symm.trans e.property⟩
    simpa only [v,localWord_on E cubic owner g _ e true,ite_true] using congrFun same v

/-- Individual entries are indexed by actual list occurrences, including
repeated entries. Fixed, possibly signed weights are allowed; only
the fixed local supported pattern of each occurrence matters. -/
structure DirectLists (R : Type*) [CommSemiring R] (owner : TriVertex V→G) where
  len : G→ℕ
  entry : ∀ g, Fin (len g)→(TriVertex V→Bool)→R
  supportWord : ∀ g, Fin (len g)→{v : TriVertex V // owner v=g}→Bool
  locality : ∀ g j σ τ, (∀ v, owner v=g → σ v=τ v) → entry g j σ=entry g j τ
  onlyWord : ∀ g j σ, entry g j σ≠0 → ∀ v : {v : TriVertex V // owner v=g},
    σ v.val=supportWord g j v

variable (L : DirectLists R owner)

def groupValue (g : G) (σ : TriVertex V→Bool) : R := ∑ j, L.entry g j σ

omit [Fintype G] [DecidableEq V] [DecidableEq G] [Nontrivial R] in
theorem groupValue_local : UsesOnly owner (groupValue owner L) := by
  intro g σ τ same
  apply Finset.sum_congr rfl
  exact fun j _ => L.locality g j σ τ same

theorem direct_list_capacity
    (correct : ∀ σ, (∏ g, groupValue owner L g σ)=UD E cubic R σ)
    (g : G) :
    3^(Fintype.card (LocalPairs E cubic owner g))≤L.len g := by
  let X := LocalPairs E cubic owner g→AllowedPair
  have mono (e : E) := exterior_pair_same_group E cubic owner (groupValue owner L)
    (groupValue_local owner L) correct e
  have existsHit (x : X) : ∃ j : Fin (L.len g), L.entry g j (localWord E cubic owner g x)≠0 := by
    by_contra! zero
    have die : groupValue owner L g (localWord E cubic owner g x)=0 := by
      simp [groupValue,zero]
    have kill : (∏ j : G, groupValue owner L j (localWord E cubic owner g x))=0 :=
      Finset.prod_eq_zero (i:=g) (Finset.mem_univ g) die
    exact one_ne_zero ((UD_localWord E cubic owner (R:=R) g x).symm.trans ((correct _).symm.trans kill))
  choose p hp using existsHit
  have hinj : Function.Injective p := by
    intro a b eq
    apply localWords_injective E cubic owner mono g
    funext v
    exact (L.onlyWord g (p a) _ (hp a) v).trans <|
      (congrArg (fun j => L.supportWord g j v) eq).trans (L.onlyWord g (p b) _ (hp b) v).symm
  have hc := Fintype.card_le_of_injective p hinj
  simpa only [X,Fintype.card_fun,allowedPairs,Fintype.card_fin] using hc

theorem local_pairs_partition :
    (∑ g : G, Fintype.card (LocalPairs E cubic owner g))=Fintype.card E := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun e : E => owner (seat E cubic e false)))

theorem many_group_pairs [Fintype V] [Nonempty G] :
    ∃ g, Fintype.card (TriVertex V)≤2*Fintype.card G*Fintype.card (LocalPairs E cubic owner g) := by
  obtain ⟨g,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset G)
    (fun j => Fintype.card (LocalPairs E cubic owner j)) Finset.univ_nonempty
  have hc : Fintype.card E≤Fintype.card G*Fintype.card (LocalPairs E cubic owner g) := by
    rw [← local_pairs_partition E cubic owner]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum (fun j hj => hmax j hj) :
        (∑ j : G, Fintype.card (LocalPairs E cubic owner j)) ≤
          ∑ _j : G, Fintype.card (LocalPairs E cubic owner g))
  refine ⟨g,?_⟩
  rw [← Fintype.card_congr (exteriorPort E cubic),Fintype.card_prod,Fintype.card_bool,Nat.mul_comm _ 2,Nat.mul_assoc]
  exact Nat.mul_le_mul_left 2 hc

#print axioms exterior_pair_same_group
#print axioms allowedPairs
#print axioms localWord_on
#print axioms UD_localWord
#print axioms localWords_injective
#print axioms groupValue_local
#print axioms direct_list_capacity
#print axioms local_pairs_partition
#print axioms many_group_pairs

end
end V8NativeMessage.N6D
