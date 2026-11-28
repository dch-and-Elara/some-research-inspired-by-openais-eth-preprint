import V8NativeMessageC3Native

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

/-! Original C3 quantifiers: after selecting one private point in every
MAIN group, the switch factors can split inside each group. Only the D
side needs a group-union cut; no alignment of MAIN groups is assumed. -/
namespace V8NativeMessage.C3
open scoped Classical BigOperators Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin
open V8PooledMenu.FiveCopy V8NativeMessage.Five
noncomputable section

section MainOnly
variable {V E G J : Type*} [Fintype V] [Fintype G] [CommRing J] {b : G→ℕ}
variable (F : MainLists (V:=V) (J:=J) b)

def pointRows (pins : Finset V) (x : V→Bool) (g : G) (k : Fin (b g)) : J :=
  F.fixed g k * ∏ v ∈ (Finset.univ : Finset {v // F.owner v=g}).filter (fun v => v.val∈pins),
    switch (x v.val) (F.θ₁ g k v.val) (F.θ₂ g k v.val)

def pointCols (pins : Finset V) (y : V→Bool) (g : G) (k : Fin (b g)) : J :=
  ∏ v ∈ (Finset.univ : Finset {v // F.owner v=g}).filter (fun v => v.val∉pins),
    switch (y v.val) (F.θ₁ g k v.val) (F.θ₂ g k v.val)

omit [Fintype G] in
theorem split_inside_main_group (pins : Finset V) (s x y : V→Bool) (g : G) (k : Fin (b g))
    (row : ∀ v∈pins, s v=x v) (col : ∀ v∉pins, s v=y v) :
    mainPoint F s g k=pointRows F pins x g k * pointCols F pins y g k := by
  let C := (Finset.univ : Finset {v // F.owner v=g}).filter (fun v => v.val∈pins)
  have comp : Cᶜ = (Finset.univ : Finset {v // F.owner v=g}).filter (fun v => v.val∉pins) := by
    ext v
    simp [C]
  unfold mainPoint pointRows pointCols
  rw [← Finset.prod_mul_prod_compl C,comp,mul_assoc]
  apply congrArg (F.fixed g k * ·)
  apply congrArg₂ (· * ·)
  · refine Finset.prod_congr rfl (fun v hv => ?_)
    rw [row v.val (Finset.mem_filter.mp hv).2]
  · refine Finset.prod_congr rfl (fun v hv => ?_)
    rw [col v.val (Finset.mem_filter.mp hv).2]

variable {G₀ : Graph V E} {m : ℕ} (M : Pairs G₀ m)

def matchRowPins : Finset V := Finset.univ.image (fun j => M.seat (j,false))

omit [Fintype V] [Fintype G] in
theorem row_pins_agree (x y : Fin m→Bool) (v : V) (hv : v∈matchRowPins M) :
    activeSigns M x y v=activeSigns M x (fun _=>false) v := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
  rw [activeSigns_left,activeSigns_left]

omit [Fintype V] [Fintype G] in
theorem col_pins_agree (x y : Fin m→Bool) (v : V) (hv : v∉matchRowPins M) :
    activeSigns M x y v=activeSigns M (fun _=>false) y v := by
  by_cases hs : v∈Set.range M.seat
  · obtain ⟨⟨j,tag⟩,rfl⟩ := hs
    cases tag
    · exact (hv (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)).elim
    · rw [activeSigns_right,activeSigns_right]
  · simp only [activeSigns,liftPairs_off M _ v hs]

def pinRowJet (x : Fin m→Bool) (q : (g : G)→Fin (b g)) : J :=
  ∏ g, pointRows F (matchRowPins M) (activeSigns M x (fun _=>false)) g (q g)

def pinColJet (y : Fin m→Bool) (q : (g : G)→Fin (b g)) : J :=
  ∏ g, pointCols F (matchRowPins M) (activeSigns M (fun _=>false) y) g (q g)

theorem main_arbitrary_cut (x y : Fin m→Bool) :
    mainCompleted F (activeSigns M x y) =
      ∑ q : ((g : G)→Fin (b g)), pinRowJet F M x q * pinColJet F M y q := by
  rw [fixed_choices]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  unfold pinRowJet pinColJet
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun g _ =>
    split_inside_main_group F _ _ _ _ g (q g) (row_pins_agree M x y) (col_pins_agree M x y))

end MainOnly

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable {K Gₘ : Type*} [Field K] [Fintype Gₘ] {m : ℕ}
variable (M : Pairs G m) (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (i : Fin (rootU V)) (T : Finset (Fin 64))
    (probes : Probes V f) (hf : f.Monic)

theorem pointwise_C3_factor_cut {J : Type*} [CommRing J] [Algebra K J] {b : Gₘ→ℕ}
    (lists : MainLists (V:=V) (J:=J) b) (ρ : J→ₗ[K]K)
    (lift : Fin 64 → HighChildView P hu huM i f → K)
    (hd : 0<f.natDegree) (dcross : Crosses M P i T) (x y : Fin m→Bool) :
    sourceBlock P hu huM i probes hf lists ρ lift (activeSigns M x y) =
      ∑ q : ((g : Gₘ)→Fin (b g)), ρ (pinRowJet lists M x q * pinColJet lists M y q) *
        (Dleft P hu huM i T probes hf lift (matchRow M P i T x) *
          Dright P hu huM i T probes hf lift (matchCol M P i T y)) := by
  have ed := C3_D_separate_lifts P hu huM i T probes hf hd lift
    (matchRow M P i T x) (matchCol M P i T y)
  rw [matchSigns M P i T dcross] at ed
  rw [sourceBlock,main_arbitrary_cut lists M x y,map_sum,Finset.sum_mul,ed]
  rfl

variable {H O : Type*} [Fintype H] [CommRing O] [Algebra O K]
variable (χ : O→+*ZMod 2) (hinj : Function.Injective (algebraMap O K))
variable (κ : H→ℕ) (b : H→Gₘ→ℕ) {J : H→Type*}
variable [∀ h, CommRing (J h)] [∀ h, Algebra K (J h)]

include hinj in
/-- Same actual count and D addresses, without any MAIN group-union
hypothesis. MAIN private lists and their port-jet data must stay fixed
independently of the signs. -/
theorem C3_literal_factor_cut
    (basis : ∀ h, Module.Basis (Fin (κ h)) K (J h))
    (lists : ∀h, MainLists (V:=V) (J:=J h) (b h)) (ρ : ∀h, J h→ₗ[K]K)
    (lift : H → Fin 64 → HighChildView P hu huM i f → K)
    (hd : 0<f.natDegree) (dcross : Crosses M P i T)
    (correct : ∀ x y, ∃ o : O, algebraMap O K o=
      (∑ h, sourceBlock P hu huM i probes hf (lists h) (ρ h) (lift h) (activeSigns M x y)) ∧
        χ o=(originCount G p (activeSigns M x y):ZMod 2)) :
    2^m≤∑h, κ h * ∏g, b h g := by
  let L (h : H) (q : Choices b h) (x : Fin m→Bool) : J h := pinRowJet (lists h) M x q
  let R (h : H) (q : Choices b h) (y : Fin m→Bool) : J h := pinColJet (lists h) M y q
  let dr (h : H) (x : Fin m→Bool) : K :=
    Dleft P hu huM i T probes hf (lift h) (matchRow M P i T x)
  let dc (h : H) (y : Fin m→Bool) : K :=
    Dright P hu huM i T probes hf (lift h) (matchCol M P i T y)
  apply C3_rank_budget κ b p M χ hinj basis ρ L R dr dc
  intro x y
  obtain ⟨o,ho,he⟩ := correct x y
  refine ⟨o,ho.trans ?_,he⟩
  simp only [Matrix.sum_apply,mixedTerm,Matrix.of_apply]
  exact Finset.sum_congr rfl (fun h _ =>
    pointwise_C3_factor_cut M P hu huM i T probes hf (lists h) (ρ h) (lift h) hd dcross x y)

#print axioms split_inside_main_group
#print axioms row_pins_agree
#print axioms col_pins_agree
#print axioms main_arbitrary_cut
#print axioms pointwise_C3_factor_cut
#print axioms C3_literal_factor_cut
end
end V8NativeMessage.C3