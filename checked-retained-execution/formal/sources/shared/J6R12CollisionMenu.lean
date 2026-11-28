import J6R12CollisionGreedyStep

/-!
# Metered generation of all binary label words

The source alphabet has 64 symbols, so an a-symbol label has exactly
6a bits, and every such tape is valid. This machine generates the
entire menu instead of treating it as an uncharged input table.
-/

namespace J6R12CollisionMenu
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep

def binaryMenu : ℕ→List (List Bool)
  | 0 => [[]]
  | b+1 =>
    let xs := binaryMenu b
    xs.map (false::·) ++ xs.map (true::·)

theorem binary_length (b : ℕ) : (binaryMenu b).length=2^b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [binaryMenu,List.length_append,List.length_map,ih,pow_succ]
    omega

theorem binary_mem (b : ℕ) (xs : List Bool) : xs ∈ binaryMenu b ↔ xs.length=b := by
  induction b generalizing xs with
  | zero => simp [binaryMenu]
  | succ b ih =>
    cases xs with
    | nil => simp [binaryMenu]
    | cons a xs => cases a <;> simp [binaryMenu,ih]

theorem binary_nodup (b : ℕ) : (binaryMenu b).Nodup := by
  induction b with
  | zero => simp [binaryMenu]
  | succ b ih =>
    rw [binaryMenu,List.nodup_append]
    refine ⟨ih.map (fun _ _ h => (List.cons.inj h).2),
      ih.map (fun _ _ h => (List.cons.inj h).2),?_⟩
    intro x hx y hy he
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
    exact Bool.false_ne_true (List.cons.inj he).1

def prefixMeter (b : ℕ) (v : Bool) (l : List (List Bool)) : Meter (List (List Bool)) :=
  mapMeter (fun q => ⟨v::q,2*b+5⟩) l

def menuMachine : ℕ→Meter (List (List Bool))
  | 0 => ⟨[[]],4⟩
  | b+1 =>
    let xs := menuMachine b
    let a := prefixMeter b false xs.result
    let c := prefixMeter b true xs.result
    ⟨a.result++c.result,xs.steps+a.steps+c.steps+4*xs.result.length+8⟩

theorem menuMachine_exact (b : ℕ) :
    (menuMachine b).result=binaryMenu b ∧ (menuMachine b).steps≤16*(b+1)*2^b := by
  induction b with
  | zero => decide
  | succ b ih =>
    let xs := menuMachine b
    let a := prefixMeter b false xs.result
    let c := prefixMeter b true xs.result
    have ha := mapMeter_exact (fun q : List Bool => ⟨false::q,2*b+5⟩)
      (false::·) (2*b+5) xs.result (fun _ _ => ⟨rfl,le_rfl⟩)
    have hc := mapMeter_exact (fun q : List Bool => ⟨true::q,2*b+5⟩)
      (true::·) (2*b+5) xs.result (fun _ _ => ⟨rfl,le_rfl⟩)
    have hR : xs.result=binaryMenu b := ih.1
    have hL : xs.result.length=2^b := by rw [hR,binary_length]
    have hA : a.result=xs.result.map (false::·) ∧ a.steps≤(2*b+5+6)*xs.result.length := ha
    have hC : c.result=xs.result.map (true::·) ∧ c.steps≤(2*b+5+6)*xs.result.length := hc
    have hX : xs.steps≤16*(b+1)*2^b := ih.2
    refine ⟨?_,?_⟩
    · change a.result++c.result=binaryMenu (b+1)
      rw [hA.1,hC.1,hR,binaryMenu]
    · change xs.steps+a.steps+c.steps+4*xs.result.length+8≤16*(b+1+1)*2^(b+1)
      rw [pow_succ,hL]
      have hb : 1≤(2:ℕ)^b := Nat.succ_le_of_lt (by positivity)
      have hAs := hA.2
      have hCs := hC.2
      rw [hL] at hAs hCs
      nlinarith

theorem equal_width_inj {xs ys : List Bool} (h : xs.length=ys.length)
    (hv : bitsValue xs=bitsValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    exact (List.length_eq_zero_iff.mp h.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have he : xs.length=ys.length := by simpa using h
      cases x <;> cases y
      all_goals
        simp only [bitsValue,Bool.toNat_false,Bool.toNat_true] at hv
        first | omega | exact congrArg (_::·) (ih he (by omega))

private theorem lift_menu {X Y : Type*} (f : X→Y) (ys : List Y)
    (h : ∀ y ∈ ys, ∃ x, f x=y) : ∃ xs : List X, xs.map f=ys := by
  induction ys with
  | nil => exact ⟨[],rfl⟩
  | cons y ys ih =>
    obtain ⟨x,rfl⟩ := h y List.mem_cons_self
    obtain ⟨xs,rfl⟩ := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    exact ⟨x::xs,rfl⟩

theorem full_alphabet {E R C A : Type*} [Fintype E] [Fintype A] (F : Format E R C A)
    (hN : Fintype.card A=2^F.b) :
    ∃ first : A, ∃ rest : List A,
      (menuMachine F.b).result=F.label first::rest.map F.label ∧
      (first::rest).Nodup ∧ (∀ a : A, a ∈ first::rest) ∧
      (menuMachine F.b).steps≤16*(F.b+1)*Fintype.card A := by
  let u : A→Fin (2^F.b) := fun a => ⟨F.aCode a,F.aFit a⟩
  have hu : Function.Injective u := fun _ _ hh => F.aInj (congrArg Fin.val hh)
  have hEq : Fintype.card A=Fintype.card (Fin (2^F.b)) := by simpa using hN
  have sur : Function.Surjective u := ((Fintype.bijective_iff_injective_and_card u).mpr ⟨hu,hEq⟩).2
  have hImg (s : List Bool) (hs : s ∈ binaryMenu F.b) : ∃ a, F.label a=s := by
    have hL := (binary_mem _ _).mp hs
    have hS : bitsValue s<2^F.b := by rw [← hL]; exact bitsValue_lt _
    obtain ⟨a,h⟩ := sur ⟨bitsValue s,hS⟩
    have hv : F.aCode a=bitsValue s := congrArg Fin.val h
    refine ⟨a,equal_width_inj ?_ ?_⟩
    · rw [Format.label,encodeBits_length,hL]
    · rw [Format.label,encodeBits_exact _ _ (F.aFit a),hv]
  have hInj : Function.Injective F.label := by
    intro x y h
    have hv := congrArg bitsValue h
    change bitsValue (encodeBits F.b (F.aCode x)) = bitsValue (encodeBits F.b (F.aCode y)) at hv
    rw [encodeBits_exact _ _ (F.aFit x),encodeBits_exact _ _ (F.aFit y)] at hv
    exact F.aInj hv
  obtain ⟨xs,hxs⟩ := lift_menu F.label (binaryMenu F.b) hImg
  have hd : xs.Nodup := by
    have hh := binary_nodup F.b
    rw [← hxs] at hh
    exact hh.of_map _
  have hAll (a : A) : a ∈ xs := by
    have hh : F.label a ∈ binaryMenu F.b := (binary_mem ..).mpr (encodeBits_length ..)
    rw [← hxs] at hh
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    rwa [← hInj he]
  obtain ⟨hG,hCost⟩ := menuMachine_exact F.b
  rw [← hxs] at hG
  rw [← hN] at hCost
  cases xs with
  | nil =>
    have hlen := binary_length F.b
    have hpos : 0<(2:ℕ)^F.b := by positivity
    rw [← hxs] at hlen
    simp at hlen
    omega
  | cons x xs => exact ⟨x,xs,hG,hd,hAll,hCost⟩

/-- Literal entropy identity for the printed 64-symbol alphabet. -/
theorem source_alphabet {G : Type*} [Fintype G] (hG : Fintype.card G=64) (a : ℕ) :
    Fintype.card (Fin a→G)=2^(6*a) := by
  rw [Fintype.card_fun,Fintype.card_fin,hG,pow_mul]
  norm_num

#print axioms binary_length
#print axioms binary_mem
#print axioms binary_nodup
#print axioms menuMachine_exact
#print axioms full_alphabet
#print axioms source_alphabet

end J6R12CollisionMenu
