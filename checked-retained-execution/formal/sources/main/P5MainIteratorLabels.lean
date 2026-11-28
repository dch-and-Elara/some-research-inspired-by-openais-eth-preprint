import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Copy-independent ordered cell labels, and the true orbit key for
coordinate swaps. The common first word prevents a variable from appearing
twice in the same copy-and-orbit. -/
namespace P5MainIterator
open scoped Classical

variable {I B : Type*} [LinearOrder B]

abbrev SortedPair (B : Type*) [LinearOrder B] := {p : B × B // p.1 ≤ p.2}

def sortedKey (p : B × B) : SortedPair B :=
  if h : p.1≤p.2 then ⟨p,h⟩ else ⟨p.swap,le_of_not_ge h⟩

abbrev WordCell (I B : Type*) := I → B × B

def orbitKey (u : WordCell I B) : I → SortedPair B := fun i => sortedKey (u i)

abbrev Unequal {I B : Type*} [LinearOrder B] (o : I → SortedPair B) :=
  {i : I // (o i).val.1 ≠ (o i).val.2}

abbrev OrbitCell (I B : Type*) [LinearOrder B] :=
  Σ o : I → SortedPair B, Unequal o → Bool

def encodeOrbit (u : WordCell I B) : OrbitCell I B :=
  ⟨orbitKey u,fun i => decide ((u i.val).2 < (u i.val).1)⟩

noncomputable def decodeOrbit (u : OrbitCell I B) : WordCell I B :=
  fun i => if h : (u.1 i).val.1 ≠ (u.1 i).val.2 then
    if u.2 ⟨i,h⟩ then (u.1 i).val.swap else (u.1 i).val
   else (u.1 i).val

theorem decode_encodeOrbit (u : WordCell I B) : decodeOrbit (encodeOrbit u)=u := by
  funext i
  by_cases hl : (u i).1 ≤ (u i).2
  · have hr : ¬(u i).2<(u i).1 := not_lt_of_ge hl
    simp [decodeOrbit,encodeOrbit,orbitKey,sortedKey,hl,hr]
  · have hr : (u i).2<(u i).1 := lt_of_not_ge hl
    have hn : (u i).2 ≠ (u i).1 := hr.ne
    simp [decodeOrbit,encodeOrbit,orbitKey,sortedKey,hl,hr,hn]

theorem encodeOrbit_injective : Function.Injective (encodeOrbit (I:=I) (B:=B)) :=
  Function.LeftInverse.injective (decode_encodeOrbit (I:=I) (B:=B))

theorem sorted_first_injective (u v : B × B) (huv : u.1=v.1)
    (hkey : sortedKey u=sortedKey v) : u=v := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨a',c⟩
  change a=a' at huv
  subst a'
  have h₁ := congrArg (fun p : SortedPair B => p.val.1) hkey
  have h₂ := congrArg (fun p : SortedPair B => p.val.2) hkey
  refine Prod.ext (show (a,b).1=(a,c).1 from rfl) ?_
  change b=c
  by_cases hl : a≤b <;> by_cases hr : a≤c <;> simp only [sortedKey,hl,hr,dif_pos,Prod.swap] at h₁ h₂
  · exact h₂
  · exact h₂.trans h₁
  · exact h₁.trans h₂
  · exact h₁

/-- Full label first word and swap-orbit key recover the original pair
of words, not only the unequal-coordinate count. -/
theorem first_and_orbit_injective (u v : WordCell I B)
    (hfirst : ∀ i, (u i).1=(v i).1) (hkey : orbitKey u=orbitKey v) : u=v := by
  funext i
  exact sorted_first_injective _ _ (hfirst i) (congrFun hkey i)

/-- The number of active coordinates is precisely the number of unequal
letter pairs of the literal cell. -/
theorem unequal_at_key_iff (u : WordCell I B) (i : I) :
    ((orbitKey u i).val.1 ≠ (orbitKey u i).val.2) ↔ (u i).1≠(u i).2 := by
  by_cases h : (u i).1≤(u i).2
  · simp [orbitKey,sortedKey,h]
  · simp [orbitKey,sortedKey,h,ne_comm]

#print axioms decode_encodeOrbit
#print axioms encodeOrbit_injective
#print axioms first_and_orbit_injective
#print axioms unequal_at_key_iff
end P5MainIterator
