import V8NativeMessageChildMenu

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! Optional literal-function reading of "one distinct Boolean tile form".
The tags remain a public upper catalogue; this proof also allows two
different catalogue labels whose functions agree on every local state. -/
namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open V8PooledMenu
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G]
  [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]}
variable {S R : Type*} [CommRing S] [CommRing R]

def AgreeForms (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (c d : TileForm P i) : Prop :=
  ∀ v : PhysicalState P i g, formValue (R:=ZMod 2) P i c (fillColumn P i g v) =
    formValue (R:=ZMod 2) P i d (fillColumn P i g v)

def RestrictedSemantic (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (β : Mode i p P.mask →₀ ℕ) (g : G) : Prop :=
  TargetActive P i β g ∨
    ∀ m n, SourceActive P i β g m → SourceActive P i β g n →
      AgreeForms P i g (modeForm P i m) (modeForm P i n)

omit [Fintype A] [Fintype B] in
theorem tagged_is_semantic (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (β : Mode i p P.mask →₀ ℕ) (g : G) (h : RestrictedChild P i β g) :
    RestrictedSemantic P i β g := by
  rcases h with h | h
  · exact Or.inl h
  · right
    intro m n hm hn v
    rw [h m n hm hn]

omit [Fintype A] [Fintype B] in
theorem source_semantic_marker (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (v : PhysicalState P i g)
    (ψ : R →+* S) (hc : (2:S)=0) (m : Mode i p P.mask) (hm : SourceActive P i β g m)
    (same : ∀ n, SourceActive P i β g n → AgreeForms P i g (modeForm P i n) (modeForm P i m)) :
    (∏ k, ∏ n∈Finset.univ.filter (fun n => childSource P i n=(g,k)),
      ψ (stateMoment P i g p v n)^β n) =
        ∏ k, parityMap hc (marker P i g (some (modeForm P i m)) k v) := by
  let value := formValue (R:=S) P i (modeForm P i m) (fillColumn P i g v)
  have em (n : Mode i p P.mask) (hn : SourceActive P i β g n) :
      ψ (stateMoment P i g p v n)=value := by
    have e := congrArg (parityMap hc) (same n hn v)
    simpa only [map_formValue,
      literal_moment_charTwo ψ hc P i p g v n hn.1,value] using e
  have echoose (k : Page a P.copies G) :
      parityMap hc (marker P i g (some (modeForm P i m)) k v) =
        if k=m.page then value else 1 := by
    by_cases hk : k=m.page
    · rw [marker,if_pos (show k=(modeForm P i m).1 from hk),if_pos hk,map_formValue]
    · rw [marker,if_neg (show k≠(modeForm P i m).1 from hk),if_neg hk,map_one]
  have hmarker : (∏ k : Page a P.copies G, if k=m.page then value else 1)=value := by
    rw [Finset.prod_eq_single m.page]
    · exact if_pos rfl
    · intro k _ hk
      exact if_neg hk
    · intro hn
      exact (hn (Finset.mem_univ m.page)).elim
  simp only [echoose,hmarker]
  rcases formValue_binary hc P i (modeForm P i m) (fillColumn P i g v) with e | e
  · change value=0 at e
    rw [e]
    apply Finset.prod_eq_zero (Finset.mem_univ m.page)
    have hmem : m∈Finset.univ.filter (fun n => childSource P i n=(g,m.page)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ m,Prod.ext hm.1 rfl⟩
    exact Finset.prod_eq_zero hmem (by rw [em m hm,e,zero_pow hm.2])
  · change value=1 at e
    rw [e]
    apply Finset.prod_eq_one
    intro k _
    apply Finset.prod_eq_one
    intro n hn
    have hs := congrArg Prod.fst (Finset.mem_filter.mp hn).2
    by_cases hb : β n=0
    · rw [hb,pow_zero]
    · rw [em n ⟨hs,hb⟩,e,one_pow]

theorem child_readout_total (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) (hc : (2:S)=0)
    (htarg : ¬ TargetActive P i β g) (c : Option (TileForm P i))
    (hsrc : ∀ v : PhysicalState P i g,
      (∏ k, ∏ m∈Finset.univ.filter (fun m => childSource P i m=(g,k)),
        ψ (stateMoment P i g p v m) ^ β m) =
        ∏ k, parityMap hc (marker P i g c k v)) :
    projectedChild P i ht hv p hp z (binaryFile f p₀ flags) hf β g ψ =
     parityMap hc (childParity P i t flags g c) := by
  rw [projectedChild_eq]
  unfold childParity
  simp only [map_sum,map_mul,map_prod]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [binary_old_projection P i g p₀ p hp₀ hf hd flags v hp ψ hc]
  apply congrArg (_ * ·)
  calc
    _ = ∏ k, parityMap hc (packetBase P i t g k v) *
      ∏ m∈Finset.univ.filter (fun m => childSource P i m=(g,k)),
        ψ (stateMoment P i g p v m)^β m := by
        refine Finset.prod_congr rfl (fun k _ => ?_)
        exact packet_projection P i ht hv p hp z β g k v ψ hc
          (fun m hm => by by_contra hn; exact htarg ⟨m,hm,hn⟩)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,hsrc v]

theorem N9_semantic_child (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) (hc : (2:S)=0)
    (hR : RestrictedSemantic P i β g) :
    projectedChild P i ht hv p hp z (binaryFile f p₀ flags) hf β g ψ =
      decodeChild P i β g (encodeChildren P i t flags) hc := by
  unfold decodeChild
  by_cases htar : TargetActive P i β g
  · rw [if_pos htar]
    obtain ⟨m,hm,hpos⟩ := htar
    exact target_child_zero P i ht hv p hp z _ hf β g ψ hc m hm hpos
  · rw [if_neg htar]
    have hsingle := hR.resolve_left htar
    by_cases hsrc : ∃ m, SourceActive P i β g m
    · rw [dif_pos hsrc]
      let m := hsrc.choose
      have hm : SourceActive P i β g m := hsrc.choose_spec
      have hg : formSource P i (modeForm P i m)=g := (formSource_mode P i m).trans hm.1
      change _ = parityMap hc (childParity P i t flags (formSource P i (modeForm P i m))
        (some (modeForm P i m)))
      rw [hg]
      exact child_readout_total P i ht hv p hp z p₀ hp₀ hf hd flags β g ψ hc htar
        (some (modeForm P i m))
        (fun v => source_semantic_marker P i p β g v ψ hc m hm (fun n hn => hsingle n m hn hm))
    · rw [dif_neg hsrc]
      exact child_readout P i ht hv p hp z p₀ hp₀ hf hd flags β g ψ hc htar none
        (fun v k => source_none P i p β g k v ψ hc hsrc)

#print axioms tagged_is_semantic
#print axioms source_semantic_marker
#print axioms child_readout_total
#print axioms N9_semantic_child
end
end V8NativeMessage