import V8NativeMessageC2PhysicalDensity
import V8NativeMessageC2PhysicalGreedy
import V8PooledRangeExpansion
import V8NativeMessageC3Rank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

/-! The same frozen five-copy packing and any selected printed active
coordinate supply the original C2 witness. The finite boundary and
matching constant are exact; no probability or concentration premise
apart from the existing layout's variance receipt is introduced. -/
namespace V8NativeMessage.C2Physical
open scoped Classical BigOperators
open V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy V8NativeMessage.Five
noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}

omit [Fintype E] in
theorem side_true_card (S : Finset V) : Fintype.card (Split.Part (cutLabel S) true)=S.card := by
  rw [Fintype.card_subtype]
  congr 1
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,cutLabel_eq_true]

omit [Fintype E] in
theorem side_false_card (S : Finset V) :
    Fintype.card (Split.Part (cutLabel S) false)=Fintype.card V-S.card := by
  rw [Fintype.card_subtype]
  have h : ((Finset.univ : Finset V).filter (fun v => cutLabel S v=false))=Sᶜ := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,cutLabel_eq_false,Finset.mem_compl]
  rw [h,Finset.card_compl]

omit [Fintype V] in
theorem boundary_card (G : Graph V E) (S : Finset V) :
    Fintype.card (Split.Cross G (cutLabel S))=(boundary G S).card := by
  rw [Fintype.card_subtype]
  rfl

def ExpansionOn {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (G : Graph V E) (γ : K) : Prop :=
  ∀ S : Finset V, γ*(min S.card (Fintype.card V-S.card):ℕ)≤((boundary G S).card:K)

theorem from_source_expansion {γ : ℚ} (h : Split.Expansion G γ) : ExpansionOn G γ := by
  intro S
  have he := h (cutLabel S)
  rw [side_false_card,side_true_card,min_comm,boundary_card] at he
  exact he

def switchUnion (P : Packing G p) (i : Fin (rootU V)) (T : Finset (Fin 64)) : Finset V :=
  BalancedUnion.vertexUnion (switchGroup P (physIndex i)) T

omit [Fintype E] in
theorem mem_switch_union (P : Packing G p) (i : Fin (rootU V)) (T : Finset (Fin 64)) (v : V) :
    v∈switchUnion P i T ↔ switchGroup P (physIndex i) v∈T := by
  simp only [switchUnion,BalancedUnion.vertexUnion,Finset.mem_filter,Finset.mem_univ,true_and]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A cut with genuinely original paired endpoints, in the same D layout
as downstream C3/N8. The fields do not carry a free geometric callback. -/
structure NativeCut (P : Packing G p) (i : Fin (rootU V)) (γ : K) where
  T : Finset (Fin 64)
  m : ℕ
  pairs : Pairs G m
  crossing : Crosses pairs P i T
  balanced : Fintype.card V≤4*min (switchUnion P i T).card (Fintype.card V-(switchUnion P i T).card)
  boundary_budget : (boundary G (switchUnion P i T)).card≤17*m
  match_budget : γ*(Fintype.card V:K)≤68*(m:K)

theorem native_cut_of_balanced (P : Packing G p) (i : Fin (rootU V)) (γ : K)
    (hγ : 0≤γ) (hE : ExpansionOn G γ) (hloop : ∀ e, G e false≠G e true)
    (T : Finset (Fin 64))
    (bal : Fintype.card V≤4*min (switchUnion P i T).card
      (Fintype.card V-(switchUnion P i T).card)) : Nonempty (NativeCut P i γ) := by
  let S := switchUnion P i T
  obtain ⟨m,chart,hb,hl,hr⟩ := crossing_pairs G S hloop p
  let b := min S.card (Fintype.card V-S.card)
  have hb' : (Fintype.card V:K)≤4*(b:K) := by exact_mod_cast bal
  have hE' : γ*(b:K)≤((boundary G S).card:K) := hE S
  have hc : ((boundary G S).card:K)≤17*(m:K) := by exact_mod_cast hb
  have hbudget : γ*(Fintype.card V:K)≤68*(m:K) := by
    calc
      _ ≤ γ*(4*(b:K)) := mul_le_mul_of_nonneg_left hb' hγ
      _ = 4*(γ*(b:K)) := by ring
      _ ≤ 4*((boundary G S).card:K) := mul_le_mul_of_nonneg_left hE' (by norm_num)
      _ ≤ 4*(17*(m:K)) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = _ := by ring
  exact ⟨⟨T,m,chart,⟨fun j => (mem_switch_union P i T _).mp (hl j),
    fun j hm => hr j ((mem_switch_union P i T _).mpr hm)⟩,bal,hb,hbudget⟩⟩

theorem native_cut_exists (P : Packing G p) (i : Fin (rootU V)) (γ : K)
    (hγ : 0≤γ) (hE : ExpansionOn G γ) (hloop : ∀ e, G e false≠G e true)
    (hN : 0<Fintype.card V) (Δ : ℕ) (hv : VarianceOK P Δ) (hm : Margin V Δ) :
    Nonempty (NativeCut P i γ) := by
  obtain ⟨T,ht⟩ := balanced_real_switch_union P Δ hv hm hN (physIndex i)
  exact native_cut_of_balanced P i γ hγ hE hloop T ht

theorem native_cut_printed_margin (P : Packing G p) (i : Fin (rootU V)) (γ : ℚ)
    (hγ : 0≤γ) (hE : Split.Expansion G γ) (hloop : ∀ e, G e false≠G e true)
    (hN : 0<Fintype.card V) (Δ : ℕ) (hv : VarianceOK P Δ)
    (hm : 2*(J9PrintedSchedule.arrayCard (rootA V))^2*Δ≤wireSize V) :
    Nonempty (NativeCut P i γ) := by
  apply native_cut_exists P i γ hγ (from_source_expansion hE) hloop hN Δ hv
  simpa only [Margin,cellCount_printed] using hm

variable {P : Packing G p} {i : Fin (rootU V)} {γ : K} (C : NativeCut P i γ)

def restrictedSigns (x y : Fin C.m→Bool) : V→Bool := activeSigns C.pairs x y

omit [IsStrictOrderedRing K] in
theorem same_native_C2_count (x y : Fin C.m→Bool) :
    originCount G p (restrictedSigns C x y)=
      3*∏ j : Fin C.m, (1+enabledPair (x j)+enabledPair (y j)) :=
  C2_count C.pairs p x y

omit [IsStrictOrderedRing K] in
theorem same_native_C2_parity (x y : Fin C.m→Bool) :
    (originCount G p (restrictedSigns C x y):ZMod 2)=(if x=y then 1 else 0) :=
  C2_parity C.pairs p x y

omit [IsStrictOrderedRing K] in
theorem same_native_C2_full_rank {O L : Type*} [CommRing O] [Field L] [Algebra O L]
    (χ : O→+*ZMod 2) (hinj : Function.Injective (algebraMap O L))
    (M : Matrix (Fin C.m→Bool) (Fin C.m→Bool) L)
    (integral : ∀ x y, ∃ o : O, algebraMap O L o=M x y ∧
      χ o=(originCount G p (restrictedSigns C x y):ZMod 2)) : M.rank=2^C.m :=
  C3.origin_parity_rank p C.pairs χ hinj M integral

#print axioms side_true_card
#print axioms side_false_card
#print axioms boundary_card
#print axioms from_source_expansion
#print axioms native_cut_of_balanced
#print axioms native_cut_exists
#print axioms native_cut_printed_margin
#print axioms same_native_C2_count
#print axioms same_native_C2_parity
#print axioms same_native_C2_full_rank
end
end V8NativeMessage.C2Physical
