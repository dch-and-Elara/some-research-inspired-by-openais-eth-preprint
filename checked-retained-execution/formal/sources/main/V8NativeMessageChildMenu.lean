import V8NativeMessageMoments
import V8NativeMessageChildProjection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6R11Blueprint V8PooledMenu
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G]
  [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]}

def TargetActive (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (β : Mode i p P.mask →₀ ℕ) (g : G) : Prop :=
  ∃ m, (childTarget P i m).1=g ∧ β m≠0

def SourceActive (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (β : Mode i p P.mask →₀ ℕ) (g : G) (m : Mode i p P.mask) : Prop :=
  (childSource P i m).1=g ∧ β m≠0

/-- Only source supports with one distinct form survive this restricted
menu. Positive target exponents may appear, but force zero. -/
def RestrictedChild (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (β : Mode i p P.mask →₀ ℕ) (g : G) : Prop :=
  TargetActive P i β g ∨
    ∀ m n, SourceActive P i β g m → SourceActive P i β g n →
      modeForm P i m=modeForm P i n

def marker (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (c : Option (TileForm P i)) (k : Page a P.copies G) (v : PhysicalState P i g) : ZMod 2 :=
  match c with
  | none => 1
  | some tag => if k=tag.1 then formValue P i tag (fillColumn P i g v) else 1

variable {S : Type*} [CommRing S] {R : Type*} [CommRing R]

omit [Fintype A] [Fintype B] in
theorem source_none (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (k : Page a P.copies G) (v : PhysicalState P i g)
    (ψ : R →+* S) (hc : (2:S)=0) (hNo : ¬ ∃ m, SourceActive P i β g m) :
    (∏ m∈Finset.univ.filter (fun m => childSource P i m=(g,k)),
      ψ (stateMoment P i g p v m) ^ β m) = parityMap hc (marker P i g none k v) := by
  rw [marker,map_one]
  apply Finset.prod_eq_one
  intro m hm
  have hs := congrArg Prod.fst (Finset.mem_filter.mp hm).2
  have hb : β m=0 := by by_contra hn; exact hNo ⟨m,hs,hn⟩
  rw [hb,pow_zero]

omit [Fintype A] [Fintype B] in
theorem source_one_form (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (k : Page a P.copies G) (v : PhysicalState P i g)
    (ψ : R →+* S) (hc : (2:S)=0) (m : Mode i p P.mask) (hm : SourceActive P i β g m)
    (single : ∀ n, SourceActive P i β g n → modeForm P i n=modeForm P i m) :
    (∏ n∈Finset.univ.filter (fun n => childSource P i n=(g,k)),
      ψ (stateMoment P i g p v n) ^ β n) =
        parityMap hc (marker P i g (some (modeForm P i m)) k v) := by
  change (childSource P i m).1=g ∧ β m≠0 at hm
  let B := Finset.univ.filter (fun n : Mode i p P.mask => childSource P i n=(g,k))
  by_cases hk : k=m.page
  · have hmB : m∈B := Finset.mem_filter.mpr ⟨Finset.mem_univ m, Prod.ext hm.1 hk.symm⟩
    let val n := ψ (stateMoment P i g p v n)
    have eqv : ∀ n∈B, β n≠0 → val n=val m := by
      intro n hn hβ
      have hsrc : (childSource P i n).1=g := congrArg Prod.fst (Finset.mem_filter.mp hn).2
      dsimp only [val]
      rw [literal_moment_charTwo ψ hc P i p g v n hsrc,
        literal_moment_charTwo ψ hc P i p g v m hm.1,single n ⟨hsrc,hβ⟩]
    have vb : val m=0 ∨ val m=1 := by
      dsimp only [val]
      rw [literal_moment_charTwo ψ hc P i p g v m hm.1]
      exact formValue_binary hc P i _ _
    have hval := powers_same_binary B val (fun n => β n) m hmB hm.2 eqv vb
    change (∏ n∈B, val n ^ β n) = _
    rw [hval,marker,show k=(modeForm P i m).1 from hk,if_pos rfl]
    dsimp only [val]
    rw [literal_moment_charTwo ψ hc P i p g v m hm.1,map_formValue]
  · change (∏ n∈B, ψ (stateMoment P i g p v n)^β n) = _
    rw [marker,if_neg (show k≠(modeForm P i m).1 from hk),map_one]
    apply Finset.prod_eq_one
    intro n hn
    have hsrc := (Finset.mem_filter.mp hn).2
    have hb : β n=0 := by
      by_contra hβ
      apply hk
      calc
        k = n.page := (congrArg Prod.snd hsrc).symm
        _ = m.page := congrArg Prod.fst (single n ⟨congrArg Prod.fst hsrc,hβ⟩)
    rw [hb,pow_zero]

/-- This is a child bit, i.e. a sum over actual group states with the
retained original clause tables. It is not the tile form itself. -/
def childParity (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) (g : G)
    (c : Option (TileForm P i)) : ZMod 2 :=
  ∑ v : PhysicalState P i g, parityBase (oldScalar P i g flags v) *
    ∏ k, packetBase P i t g k v * marker P i g c k v

theorem child_readout (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) (hc : (2:S)=0)
    (htarg : ¬ TargetActive P i β g) (c : Option (TileForm P i))
    (hsrc : ∀ v : PhysicalState P i g, ∀ k : Page a P.copies G,
      (∏ m∈Finset.univ.filter (fun m => childSource P i m=(g,k)),
        ψ (stateMoment P i g p v m) ^ β m) = parityMap hc (marker P i g c k v)) :
    projectedChild P i ht hv p hp z (binaryFile f p₀ flags) hf β g ψ =
     parityMap hc (childParity P i t flags g c) := by
  rw [projectedChild_eq]
  unfold childParity
  simp only [map_sum,map_mul,map_prod]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [binary_old_projection P i g p₀ p hp₀ hf hd flags v hp ψ hc]
  apply congrArg (_ * ·)
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [packet_projection P i ht hv p hp z β g k v ψ hc
    (fun m hm => by by_contra hn; exact htarg ⟨m,hm,hn⟩),hsrc v k]

abbrev ChildTape (P : PhysicalPacking N a G) (i : Fin a) :=
  (G → ZMod 2) × (TileForm P i → ZMod 2)

/-- At most one word per form, in its unique actual source group. -/
def encodeChildren (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) : ChildTape P i :=
  (fun g => childParity P i t flags g none,
   fun c => childParity P i t flags (formSource P i c) (some c))

def decodeChild (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (β : Mode i p P.mask →₀ ℕ) (g : G) (tape : ChildTape P i) (hc : (2:S)=0) : S :=
  if TargetActive P i β g then 0 else
  if h : ∃ m, SourceActive P i β g m then parityMap hc (tape.2 (modeForm P i h.choose))
  else parityMap hc (tape.1 g)

theorem N9_projected_child (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flags : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) (hc : (2:S)=0)
    (hR : RestrictedChild P i β g) :
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
      exact child_readout P i ht hv p hp z p₀ hp₀ hf hd flags β g ψ hc htar
        (some (modeForm P i m))
        (fun v k => source_one_form P i p β g k v ψ hc m hm (fun n hn => hsingle n m hn hm))
    · rw [dif_neg hsrc]
      exact child_readout P i ht hv p hp z p₀ hp₀ hf hd flags β g ψ hc htar none
        (fun v k => source_none P i p β g k v ψ hc hsrc)

#print axioms source_none
#print axioms source_one_form
#print axioms childParity
#print axioms child_readout
#print axioms encodeChildren
#print axioms N9_projected_child

end
end V8NativeMessage