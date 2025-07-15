import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Sublattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Order.Lattice
/-!

# Subdirect irreducibility and simplicity of lattices

We prove that there exists a lattice that is
subdirectly irreducible but not simple.

  0
 / \
|  `4`
3  `|`
|  `2`
 \ /
  1

-/

section UniversalAlgebra

/-- `R` is a congruence of the lattice `L` if it
 is an equivalence relation that preserves `∨` and `∧`. -/
def congruence {L : Type*} (l : Lattice L) (R : L → L → Prop) : Prop :=
    IsEquiv _ R ∧
    (∀ x₀ x₁ y₀ y₁, R x₀ x₁ → R y₀ y₁ → R (l.sup x₀ y₀) (l.sup x₁ y₁)) ∧
    (∀ x₀ x₁ y₀ y₁, R x₀ x₁ → R y₀ y₁ → R (l.inf x₀ y₀) (l.inf x₁ y₁))

/-- `N₅` is the 5-element nonmodular lattice.
 We realize it is `{0,1,...,4}` under divisibility `x ∣ y`.
-/
noncomputable def N₅ : Lattice (Fin 5) := {
    le := fun x y =>
        Dvd.dvd x.1 y.1 -- x.1 ∣ y.1
    lt := fun x y => Dvd.dvd x.1 y.1 ∧ ¬ Dvd.dvd y.1 x.1
    le_refl := by
        intro a
        simp
    le_antisymm := fun a b h₀ h₁ => by
        refine Fin.eq_of_val_eq ?_
        exact Nat.dvd_antisymm h₀ h₁
    sup := fun a b => by
        by_cases H₀ : a.1 = 0 ∨ b.1 = 0
        · exact 0
        · by_cases H : a.1 ∣ b.1 ∨ b.1 ∣ a.1
          · exact ⟨Nat.max a.1 b.1, by
                have ha := a.2
                have hb := b.2
                by_cases H : 0 < a.1
                · exact max_lt ha hb
                · have : a.1 = 0 := by linarith
                  rw [this]
                  simp⟩
          · exact 0
    le_trans := fun a b c h₀ h₁ => Nat.dvd_trans h₀ h₁
    le_sup_left := fun a b => by
        split_ifs with g₀ g₁ g₂
        · exact Nat.dvd_of_mod_eq_zero rfl
        · simp
          have : a.1.max b.1 = a.1 ∨ a.1.max b.1 = b.1 := max_choice a.1 b.1
          cases this with
          | inl h₀ => rw [h₀]
          | inr h₀ =>
            cases g₁ with
            | inl h₁ => rw [h₀];exact h₁
            | inr h₁ =>
                rw [h₀]
                have : a.1 = b.1 := by
                    apply le_antisymm
                    · exact le_of_sup_eq h₀
                    · exact Nat.le_of_dvd g₂ h₁
                rw [this]
        · simp_all
        · exact Nat.dvd_of_mod_eq_zero rfl
    le_sup_right := fun a b => by
        split_ifs with g₀ g₁ g₂
        · exact Nat.dvd_of_mod_eq_zero rfl
        · simp
          have : a.1.max b.1 = a.1 ∨ a.1.max b.1 = b.1 := max_choice a.1 b.1
          cases this with
          | inl h₀ =>
            rw [h₀]
            cases g₁ with
            | inl h =>
                have : a.1 = b.1 := by
                    apply le_antisymm
                    · have : b.1 ≠ 0 := by omega
                      apply Nat.le_of_dvd
                      omega
                      exact h
                    · exact sup_eq_left.mp h₀
                rw [this]

            | inr h => exact h
          | inr h₀ =>
            cases g₁ with
            | inl h₁ => rw [h₀]
            | inr h₁ =>
                rw [h₀]
        · simp_all
        · exact Nat.dvd_of_mod_eq_zero rfl
    sup_le := fun a b c h₀ h₁ => by
        split_ifs with g₀ g₁ g₂
        cases g₀ with
        | inl h => rw [h] at h₀;simp at h₀ ⊢;exact h₀
        | inr h => rw [h] at h₁;simp at h₁ ⊢;exact h₁

        · simp
          have : a.1.max b.1 = a.1 ∨ a.1.max b.1 = b.1 := max_choice a.1 b.1
          cases this with
          | inl h₀ =>
            rw [h₀]
            cases g₁ with
            | inl h =>
                have : a.1 = b.1 := by
                    apply le_antisymm
                    · have : b.1 ≠ 0 := by omega
                      apply Nat.le_of_dvd
                      omega
                      exact h
                    · exact sup_eq_left.mp h₀
                rw [this]
                exact h₁
            | inr h => tauto
          | inr h₀ =>
            cases g₁ with
            | inl h₁ => rw [h₀];tauto
            | inr h₁ =>
                rw [h₀];tauto
        · simp_all
        · fin_cases c <;> fin_cases a <;> fin_cases b <;> simp_all
    inf := fun a b => ⟨Nat.gcd a.1 b.1, by
        have ha := a.2
        have hb := b.2
        by_cases H : 0 < a.1
        · have : a.1.gcd b.1 ≤ a.1 := Nat.gcd_le_left ↑b H
          linarith
        · have : a.1 = 0 := by linarith
          rw [this]
          simp⟩
    inf_le_left := fun a b => Nat.gcd_dvd_left ↑a ↑b
    inf_le_right := fun a b => Nat.gcd_dvd_right ↑a ↑b
    le_inf := fun a b c h₀ h₁ => Nat.dvd_gcd h₀ h₁
}

/-- A lattice `L` is *subdirectly irreducible* if it contains two elements
`a, b` that are identified by any nontrivial congruence.

(We also allow the trivial case `|L| ≤ 1`.)
-/
def SubdirectlyIrreducible {A : Type*} (l : Lattice A) :=
    (∀ a b : A, a = b) ∨ ∃ a b : A, a ≠ b ∧ ∀ R, congruence l R → R ≠ Eq → R a b

/-- A lattice is simple if it has no nontrivial congruences. -/
def Simple {A : Type*} (l : Lattice A) : Prop :=
    ∀ R, congruence l R → R = Eq ∨ R = fun _ _ => True

/-- The equivalence relation that identifies two elements `x ≠ y`.
(The assumption `x ≠ y` is not strictly speaking needed.)
-/
def principalEquiv {A : Type*} (x y : A) (hxy : x ≠ y) :
    IsEquiv A fun a b ↦ a = b ∨ ({a, b} : Set A) = {x, y} := {
        refl := fun a => Or.inl rfl
        trans := fun a b c h₀ h₁ => by
          cases h₀ with
          | inl h =>
            cases h₁ with
            | inl h₂ =>
              left
              exact h.trans h₂
            | inr h₂ =>
              subst h
              tauto
          | inr h =>
            cases h₁ with
            | inl h₂ =>
              subst h₂
              right;tauto
            | inr h₂ =>
              left
              have : a = x ∨ a = y := by
                have : a ∈ ({a,b} : Set A) := by simp
                rw [h] at this
                simp at this
                tauto
              cases this with
              | inl h =>
                symm at h
                subst h
                have : b = x ∨ b = y := by
                    have : b ∈ ({b,c} : Set A) := by simp
                    rw [h₂] at this
                    simp at this
                    tauto
                cases this with
                | inl h =>
                  subst h;simp at h
                  rw [← h₂] at h
                  rw [Set.ext_iff] at h
                  specialize h c
                  simp at h
                  tauto
                | inr h =>
                  subst h
                  rw [Set.ext_iff] at h₂
                  specialize h₂ x
                  simp at h₂
                  tauto
              | inr h =>
                symm at h
                subst h
                have : b = x ∨ b = y := by
                    have : b ∈ ({b,c} : Set A) := by simp
                    rw [h₂] at this
                    simp at this
                    tauto
                cases this with
                | inl h =>
                  subst h
                  rw [← h₂] at h
                  rw [Set.ext_iff] at h
                  specialize h c
                  simp at h
                  cases h with
                  | inl h => tauto
                  | inr h =>
                    subst h
                    rw [Set.ext_iff] at h₂
                    specialize h₂ y
                    simp at h₂
                    tauto
                | inr h =>
                  subst h
                  rw [Set.ext_iff] at h
                  specialize h x
                  simp at h
                  tauto
        symm := fun a b h => by
            cases h with
            | inl h => subst h;tauto
            | inr h => right;rw [← h];ext;simp;tauto}

/-- An interval `[x,y]` is *strong* if its elements `u` agree on
whether they are above or below a given element `z ∉ [x,y]`.
The equivalence relation formed by collapsing such an interval
preserves `∨`.
-/
theorem preserve_sup_of_strong {A : Type*} (l : Lattice A) (x y : A)
  (hxy' :
    ∀ z ∉ Set.Icc x y,
      ∀ w₀ ∈ Set.Icc x y,
        ∀ w₁ ∈ Set.Icc x y, (w₀ ≤ z ↔ w₁ ≤ z) ∧ (z ≤ w₀ ↔ z ≤ w₁))
  (x₀ x₁ y₀ y₁ : A) :
  (fun a b ↦ a = b ∨ {a, b} ⊆ Set.Icc x y) x₀ x₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ Set.Icc x y) y₀ y₁ →
      (fun a b ↦ a = b ∨ {a, b} ⊆ Set.Icc x y)
      (SemilatticeSup.sup x₀ y₀) (SemilatticeSup.sup x₁ y₁) := by
  intro h₀ h₁
  cases h₀ with
  | inl h =>
    subst h
    cases h₁ with
    | inl h =>
      subst h
      tauto
    | inr h =>
      rw [Set.pair_subset_iff] at h
      by_cases H : x₀ ≤ y
      · right
        rw [Set.pair_subset_iff]
        constructor
        · constructor
          · apply le_trans h.1.1
            apply le_sup_right
          · apply sup_le H h.1.2
        · constructor
          · apply le_trans h.2.1
            apply le_sup_right
          · apply sup_le H h.2.2
      · left
        have hxy₀ := hxy' (SemilatticeSup.sup x₀ y₁) (by
          unfold Set.Icc
          simp only [Set.mem_setOf_eq]
          contrapose! H
          apply le_trans ?_ H.2
          apply le_sup_left) y₀ h.1 y₁ h.2
        have hxy₁ := hxy' (SemilatticeSup.sup x₀ y₀) (by
          unfold Set.Icc
          simp only [Set.mem_setOf_eq]
          contrapose! H
          apply le_trans ?_ H.2
          apply le_sup_left) y₀ h.1 y₁ h.2
        apply le_antisymm
        · apply sup_le
          · apply le_sup_left
          · rw [hxy₀.1]
            apply le_sup_right
        · apply sup_le
          · apply le_sup_left
          · rw [← hxy₁.1]
            apply le_sup_right
  | inr h =>
    cases h₁ with
    | inl h =>
      subst h
      by_cases H : y₀ ∈ Set.Icc x y
      · right
        rw [Set.pair_subset_iff] at h ⊢
        constructor
        · constructor
          · apply le_trans
            · change x ≤ x₀
              exact h.1.1
            apply le_sup_left
          · apply sup_le
            · exact h.1.2
            · exact H.2
        · constructor
          · apply le_trans
            · change x ≤ x₁
              exact h.2.1
            · apply le_sup_left
          · apply sup_le
            · exact h.2.2
            · exact H.2
      · by_cases H₀ : x ≤ y₀
        · left
          apply le_antisymm
          · apply sup_le
            · have := hxy' ( SemilatticeSup.sup x₁ y₀) (by
                contrapose! H
                constructor
                · tauto
                · apply le_trans
                  change _ ≤  SemilatticeSup.sup x₁ y₀
                  apply le_sup_right
                  exact H.2) x₀ (by apply h;simp) x₁ (by apply h;simp)
              apply this.1.mpr
              apply le_sup_left
            · apply le_sup_right
          · apply sup_le
            · have := hxy' ( SemilatticeSup.sup x₀ y₀) (by
                contrapose! H
                constructor
                · tauto
                · apply le_trans
                  change _ ≤  SemilatticeSup.sup x₀ y₀
                  apply le_sup_right
                  exact H.2) x₀ (by apply h;simp) x₁ (by apply h;simp)
              apply this.1.mp
              apply le_sup_left
            · apply le_sup_right
        · by_cases H₁ : y₀ ≤ y
          · right
            rw [Set.pair_subset_iff] at h ⊢
            constructor
            · constructor
              · apply le_trans
                · change _ ≤ x₀
                  exact h.1.1
                apply le_sup_left
              · apply sup_le
                · exact h.1.2
                · tauto
            · constructor
              · apply le_trans
                · change _ ≤ x₁
                  exact h.2.1
                · apply le_sup_left
              · apply sup_le
                · exact h.2.2
                · tauto
          left
          apply le_antisymm
          · apply sup_le
            · have := hxy' (SemilatticeSup.sup x₁ y₀)
                (by
                    contrapose! H₁
                    have := H₁.2
                    apply le_trans _ this
                    apply le_sup_right) x₀ (by apply h;simp) x₁
                    (by apply h;simp)
              apply this.1.mpr
              apply le_sup_left
            · apply le_sup_right

          · apply sup_le
            · have := hxy' (SemilatticeSup.sup x₀ y₀)
                (by
                    contrapose! H₁
                    have := H₁.2
                    apply le_trans _ this
                    apply le_sup_right) x₀ (by apply h;simp) x₁
                    (by apply h;simp)
              apply this.1.mp
              apply le_sup_left
            · apply le_sup_right
    | inr h' =>
      right
      rw [Set.pair_subset_iff] at h h' ⊢
      constructor
      · constructor
        · apply le_trans
          · exact h.1.1
          · apply le_sup_left
        · apply sup_le
          · exact h.1.2
          · exact h'.1.2
      · constructor
        · apply le_trans
          · exact h.2.1
          · apply le_sup_left
        · apply sup_le
          · exact h.2.2
          · exact h'.2.2


/-- Simple implies subdirectly irreducible.
(N₅ is an example of the failure of the converse.)
M₃ is simple.
-/
theorem sdi_of_simple {A : Type*} (l : Lattice A) (h : Simple l) :
    SubdirectlyIrreducible l := by
    unfold Simple SubdirectlyIrreducible at *
    by_cases H :  (∀ (a b : A), a = b)
    · tauto
    · right
      push_neg at H
      obtain ⟨a,b,hab⟩ := H
      use a, b
      constructor
      · tauto
      · intro R hR
        specialize h R hR
        intro h₀
        cases h with
        | inl h => exact (h₀ h).elim
        | inr h => exact h ▸ trivial


lemma N₅helper : {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4} = {2, 4} := by
    ext u
    simp
    constructor
    · intro h
      obtain ⟨c₀,hc₀⟩ := h.1
      obtain ⟨c₁,hc₁⟩ := h.2
      suffices (u.1 = 2) ∨ (u.1 = 4) by
        cases this with
        | inl h => left;exact Fin.eq_of_val_eq h
        | inr h => right;exact Fin.eq_of_val_eq h
      rw [hc₀] at hc₁
      have : 2 * 2 = 2 * (c₀ * c₁) := by rw [← mul_assoc];omega
      have : 2 = c₀ * c₁ := by
        have := (mul_left_cancel_iff_of_pos (show 0 < 2 by simp) (c:= 2)
          (b := c₀ * c₁)).mp this.symm
        omega
      have : c₀ ≠ 0 := by
        intro hc
        subst hc
        simp at this
      have : c₀ ∣ 2 := by (expose_names; exact Dvd.intro c₁ (id (Eq.symm this_2)))
      have : c₀ ≤ 2 := by apply Nat.le_of_dvd;simp;tauto
      have : c₀ = 1 ∨ c₀ = 2 := by omega
      cases this with
      | inl h =>
      subst h
      have : c₁ = 2 := by omega
      subst this
      left
      tauto
      | inr h =>
          subst h
          have : c₁ = 1 := by omega
          subst this
          rw [hc₀]
          simp
    intro h
    cases h with
    | inl h =>
        subst h
        change 2 ∣ 2 ∧ 2 ∣ 4
        omega
    | inr h =>
        subst h
        change 2 ∣ 4 ∧ 4 ∣ 4
        omega

open Classical in
/-- The principal equivalence relation with block `{2,4}`
preserves `∨` in `N₅`. -/
lemma N₅_congr_sup (x₀ x₁ y₀ y₁ : Fin 5) :
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) x₀ x₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) y₀ y₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4})
      (N₅.sup x₀ y₀) (N₅.sup x₁ y₁) := by
      intro h₀ h₁
      rw [N₅helper] at h₀ h₁
      cases h₀ with
      | inl h =>
        subst h
        cases h₁ with
        | inl h =>
            subst h
            left
            tauto
        | inr h =>
            by_cases H : x₀ ∈ ({2, 4} : Set (Fin 5))
            · right
              rw [N₅helper]

              rw [Set.pair_subset_iff] at h ⊢
              constructor
              · cases H with
              | inl h' =>
                subst h'
                have := h.1
                cases this with
                | inl h => subst h;simp;decide
                | inr h => simp at h;subst h;simp;decide
              | inr h =>
                simp at h
                subst h
                have := h.1
                cases this with
                | inl h => subst h;simp;decide
                | inr h => subst h;simp;decide
              · cases H with
              | inl h' =>
                subst h'
                have := h.2
                cases this with
                | inl h => subst h;simp;decide
                | inr h => simp at h;subst h;simp;decide
              | inr h =>
                simp at h
                subst h
                have := h.2
                cases this with
                | inl h => subst h;simp;decide
                | inr h => subst h;simp;decide
            · rw [Set.pair_subset_iff] at h
              simp at h H
              have h₁ := h.1
              have h₂ := h.2
              cases h₁ with
              | inl h =>
                subst h
                cases h₂ with
                | inl h =>
                    subst h
                    left
                    rfl
                | inr h =>
                    subst h
                    fin_cases x₀
                    · simp at H ⊢
                      left
                      change N₅.sup 0 2 = N₅.sup 0 4
                      decide
                    · simp at H ⊢
                      right
                      rw [N₅helper]
                      rw [Set.pair_subset_iff]
                      simp
                      decide
                    · simp at H ⊢
                    · simp at H ⊢
                      left
                      decide
                    · simp at H ⊢
              | inr h =>
                subst h
                cases h₂ with
                | inl h =>
                    subst h
                    fin_cases x₀
                    · simp at H ⊢
                      decide
                    · simp at H ⊢
                      right
                      rw [N₅helper]
                      rw [Set.pair_subset_iff]
                      simp
                      decide
                    · simp at H ⊢
                    · simp at H ⊢
                      left
                      decide
                    · simp at H ⊢
                | inr h =>
                    subst h
                    left
                    rfl

      | inr h =>
        rw [Set.pair_subset_iff] at h
        cases h₁ with
        | inl h =>
            subst h
            by_cases H : y₀.1 ∣ 4
            · right
              rw [Set.pair_subset_iff]
              constructor
              · simp
                constructor
                · change N₅.le 2 _
                  apply N₅.le_trans
                  · change N₅.le 2 x₀
                    have h₁ := h.1
                    cases h₁ with
                    | inl h => subst h;change 2 ∣ 2;simp
                    | inr h => subst h;change 2 ∣ 4;simp
                  apply N₅.le_sup_left
                · change N₅.le (N₅.sup x₀ y₀) 4
                  apply N₅.sup_le
                  · have h₁ := h.1
                    cases h₁ with
                    | inl h => subst h;change 2 ∣ 4;simp
                    | inr h => subst h;change 4 ∣ 4;simp
                  change y₀.1 ∣ 4
                  exact H
              · simp
                constructor
                · change N₅.le 2 _
                  apply N₅.le_trans
                  · change N₅.le 2 x₁
                    have h₁ := h.2
                    cases h₁ with
                    | inl h => subst h;change 2 ∣ 2;simp
                    | inr h => subst h;change 2 ∣ 4;simp
                  apply N₅.le_sup_left
                · change N₅.le (N₅.sup x₁ y₀) 4
                  apply N₅.sup_le
                  · have h₁ := h.2
                    cases h₁ with
                    | inl h => subst h;change 2 ∣ 4;simp
                    | inr h => subst h;change 4 ∣ 4;simp
                  change y₀.1 ∣ 4
                  exact H
            · left
              change N₅.sup x₀ y₀ = N₅.sup x₁ y₀
              have g₀: N₅.sup x₀ y₀ = 0 := by
                fin_cases y₀
                · simp at H ⊢
                  fin_cases x₀ <;> decide
                · simp at H ⊢
                · simp at H ⊢
                · simp at H ⊢
                  have h₁ := h.1
                  cases h₁ with
                  | inl h => subst h;decide
                  | inr h => simp at h;subst h;decide
                · simp at H ⊢
              have g₁: N₅.sup x₁ y₀ = 0 := by
                fin_cases y₀
                · simp at H ⊢
                  fin_cases x₁ <;> decide
                · simp at H ⊢
                · simp at H ⊢
                · simp at H ⊢
                  have h₁ := h.2
                  cases h₁ with
                  | inl h => subst h;decide
                  | inr h => simp at h;subst h;decide
                · simp at H ⊢
              exact g₀.trans g₁.symm
        | inr h' =>
          right
          rw [Set.pair_subset_iff] at h' ⊢
          rw [N₅helper]
          constructor
          -- done above?
          · simp
            have := h.1
            cases this with
            | inl h =>
              subst h
              have := h'.1
              cases this with
              | inl h =>
                subst h
                decide
              | inr h =>
                subst h
                decide
            | inr h =>
              subst h
              have := h'.1
              cases this with
              | inl h =>
                subst h
                decide
              | inr h =>
                subst h
                decide

          simp
          have := h.2
          cases this with
          | inl h =>
            subst h
            have := h'.2
            cases this with
            | inl h =>
                subst h
                decide
            | inr h =>
                subst h
                decide
          | inr h =>
            subst h
            have := h'.2
            cases this with
            | inl h =>
                subst h
                decide
            | inr h =>
                subst h
                decide
open Classical in
/-- The principal equivalence relation with block `{2,4}`
preserves `∧` in `N₅`. -/
lemma N₅_congr_inf (x₀ x₁ y₀ y₁ : Fin 5) :
  (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) x₀ x₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) y₀ y₁ →
      (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4})
      (N₅.inf x₀ y₀) (N₅.inf x₁ y₁) := by
      intro h₀ h₁
      rw [N₅helper] at h₀ h₁
      cases h₀ with
      | inl h =>
        subst h
        cases h₁ with
        | inl h =>
            subst h
            left
            tauto
        | inr h =>
            by_cases H : x₀ ∈ ({2, 4} : Set (Fin 5))
            · right
              rw [N₅helper]

              rw [Set.pair_subset_iff] at h ⊢
              constructor
              · cases H with
              | inl h' =>
                subst h'
                have := h.1
                cases this with
                | inl h => subst h;simp;decide
                | inr h => simp at h;subst h;simp;decide
              | inr h =>
                simp at h
                subst h
                have := h.1
                cases this with
                | inl h => subst h;simp;decide
                | inr h => subst h;simp;decide
              · cases H with
              | inl h' =>
                subst h'
                have := h.2
                cases this with
                | inl h => subst h;simp;decide
                | inr h => simp at h;subst h;simp;decide
              | inr h =>
                simp at h
                subst h
                have := h.2
                cases this with
                | inl h => subst h;simp;decide
                | inr h => subst h;simp;decide
            · rw [Set.pair_subset_iff] at h
              simp at h H
              have h₁ := h.1
              have h₂ := h.2
              cases h₁ with
              | inl h =>
                subst h
                cases h₂ with
                | inl h =>
                    subst h
                    left
                    rfl
                | inr h =>
                    subst h
                    fin_cases x₀
                    · simp at H ⊢
                      right
                      rw [N₅helper]
                      rw [Set.pair_subset_iff]
                      simp
                      decide
                    · simp at H ⊢
                      left
                      change N₅.inf 1 2 = N₅.inf 1 4
                      decide
                    · simp at H ⊢
                    · simp at H ⊢
                      left
                      decide
                    · simp at H ⊢
              | inr h =>
                subst h
                cases h₂ with
                | inl h =>
                    subst h
                    fin_cases x₀
                    · simp at H ⊢
                      right
                      rw [N₅helper]
                      rw [Set.pair_subset_iff]
                      simp
                      decide
                    · simp at H ⊢
                      decide
                    · simp at H ⊢
                    · simp at H ⊢
                      left
                      decide
                    · simp at H ⊢
                | inr h =>
                    subst h
                    left
                    rfl

      | inr h =>
        rw [Set.pair_subset_iff] at h
        cases h₁ with
        | inl h =>
            subst h
            by_cases H : 2 ∣ y₀.1
            · right
              rw [Set.pair_subset_iff]
              constructor
              · simp
                constructor
                · change N₅.le 2 (N₅.inf x₀ y₀)
                  apply N₅.le_inf
                  · have h₁ := h.1
                    cases h₁ with
                    | inl h => subst h;change 2 ∣ 2;simp
                    | inr h => subst h;change 2 ∣ 4;simp
                  change 2 ∣ y₀.1
                  exact H
                · change N₅.le (N₅.inf x₀ y₀) 4
                  apply N₅.le_trans
                  · change N₅.le _ x₀
                    have h₁ := h.1
                    cases h₁ with
                    | inl h => subst h;apply N₅.inf_le_left
                    | inr h => subst h;apply N₅.inf_le_left
                  have := h.1
                  cases this with
                  | inl h => subst h;change 2 ∣ 4;simp
                  | inr h => subst h;change 4 ∣ 4;simp
              · simp
                constructor
                · change N₅.le 2 _
                  apply N₅.le_inf
                  · change N₅.le 2 x₁
                    have h₁ := h.2
                    cases h₁ with
                    | inl h => subst h;change 2 ∣ 2;simp
                    | inr h => subst h;change 2 ∣ 4;simp
                  exact H
                · change N₅.le (N₅.inf x₁ y₀) 4
                  apply N₅.le_trans
                  · change N₅.le _ x₁
                    apply N₅.inf_le_left
                  · have := h.2
                    cases this with
                    | inl h => subst h;change 2 ∣ 4;decide
                    | inr h => subst h;change 4 ∣ 4;decide
            · left
              change N₅.inf x₀ y₀ = N₅.inf x₁ y₀
              have g₀: N₅.inf x₀ y₀ = 1 := by
                fin_cases y₀
                · simp at H ⊢
                · simp at H ⊢
                  fin_cases x₀ <;> decide
                · simp at H ⊢
                · simp at H ⊢
                  have h₁ := h.1
                  cases h₁ with
                  | inl h => subst h;decide
                  | inr h => simp at h;subst h;decide
                · simp at H ⊢
              have g₁: N₅.inf x₁ y₀ = 1 := by
                fin_cases y₀
                · simp at H ⊢
                · simp at H ⊢
                  fin_cases x₁ <;> decide
                · simp at H ⊢
                · simp at H ⊢
                  have h₁ := h.2
                  cases h₁ with
                  | inl h => subst h;decide
                  | inr h => simp at h;subst h;decide
                · simp at H ⊢
              exact g₀.trans g₁.symm
        | inr h' =>
          right
          rw [Set.pair_subset_iff] at h' ⊢
          rw [N₅helper]
          constructor
          -- done above?
          · simp
            have := h.1
            cases this with
            | inl h =>
              subst h
              have := h'.1
              cases this with
              | inl h =>
                  subst h
                  decide
              | inr h =>
                  subst h
                  decide
            | inr h =>
              subst h
              have := h'.1
              cases this with
              | inl h =>
                  subst h
                  decide
              | inr h =>
                  subst h
                  decide

          simp
          have := h.2
          cases this with
          | inl h =>
            subst h
            have := h'.2
            cases this with
            | inl h =>
                subst h
                decide
            | inr h =>
                subst h
                decide
          | inr h =>
            subst h
            have := h'.2
            cases this with
            | inl h =>
                subst h
                decide
            | inr h =>
                subst h
                decide

/-- The interval `[2,4]` in `N₅` is strong. -/
lemma N₅strongInterval (z : Fin 5) :
  z ∉ {u | 2 ∣ u.1 ∧ u.1 ∣ 4} →
    ∀ w₀ ∈ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
    ∀ w₁ ∈ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
      (w₀.1 ∣ z.1 ↔ ↑w₁ ∣ z.1) ∧ (z.1 ∣ w₀.1 ↔ z.1 ∣ ↑w₁) := by
    rw [N₅helper]
    intro hz w₀ hw₀ w₁ hw₁
    simp at hz hw₀ hw₁
    fin_cases z
    · simp at hz ⊢
      omega
    · simp at hz ⊢
      omega
    · simp at hz ⊢
    · simp at hz ⊢
      cases hw₀ with
      | inl h =>
        subst h
        simp
        cases hw₁ with
        | inl h =>
            subst h
            simp
        | inr h =>
            subst h
            change (¬ 4 ∣ 3) ∧ (¬ 3 ∣ 4)
            simp
      | inr h =>
        subst h
        cases hw₁ with
        | inl h =>
            subst h
            change  (↑4 ∣ 3 ↔ ↑2 ∣ 3) ∧ (3 ∣ ↑4 ↔ 3 ∣ ↑2)
            simp
        | inr h =>
            subst h
            simp
    · simp at hz ⊢
open Classical in
/-- The lattice `N₅` is not simple. -/
theorem not_simple_N₅ : ¬ Simple N₅ := by
  have hio := @preserve_sup_of_strong (Fin 5) N₅ 2 4
  unfold Simple
  push_neg
  use (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4})
  constructor
  · specialize hio (by
      change  ∀ z ∉ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
          ∀ w₀ ∈ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
          ∀ w₁ ∈ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
          (w₀.1 ∣ z.1 ↔ w₁.1 ∣ z.1) ∧ (z.1 ∣ w₀.1 ↔ z.1 ∣ w₁.1)
      apply N₅strongInterval)

    constructor
    · have := principalEquiv (2:Fin 5) 4 (by simp)
      rw [N₅helper]
      convert this using 1
      ext i j
      rw [Set.pair_subset_iff]
      rw [Set.pair_eq_pair_iff]
      simp
      constructor
      · intro h
        aesop
      · intro h
        aesop
    · constructor
      · apply N₅_congr_sup
      · apply N₅_congr_inf

  constructor
  · intro hc
    rw [funext_iff] at hc
    specialize hc 2
    rw [funext_iff] at hc
    specialize hc 4
    simp at hc
    apply hc
    rw [Set.pair_subset_iff]
    constructor
    · simp
    · simp
  · intro hc
    rw [funext_iff] at hc
    specialize hc 0
    rw [funext_iff] at hc
    specialize hc 1
    simp at hc
    have := hc (show 0 ∈ {0,1} by simp)
    simp at this

/-- If `R` is a congruence of a lattice `L`
 then its blocks are convex: if
 `a ≤ b ≤ c ≤ d` and `R(a,d)` then `R(b,c)`. -/
lemma ofIcc {A : Type*} {l : Lattice A} {R : A → A → Prop}
    (hR₀ : congruence l R)
    {a b c d : A} (o₀ : l.le a b) (o₁ : l.le b c) (o₂ : l.le c d)
    (h : R a d) : R b c := by
      let refl := hR₀.1.1.1.refl
      let symm := hR₀.1.2.symm
      let conJoin := hR₀.2.1
      let conMeet := hR₀.2.2
      let trans := fun {a b c} => hR₀.1.1.2.trans a b c
      -- if a=d then c = d ∧ c = a ∧ c = a:
      have h₀ : c = (l.inf d c) := by
        apply l.le_antisymm
        apply l.le_inf
        exact o₂
        apply l.le_refl
        apply l.inf_le_right
      have h₁ : R (l.inf d c) (l.inf a c) := by
        apply conMeet
        apply symm
        exact h
        apply refl
      have h₂ : (l.inf a c) = a := by
        apply l.le_antisymm
        · apply l.inf_le_left
        · apply l.le_inf
          · apply l.le_refl
          · apply l.le_trans
            · apply o₀
            · exact o₁
      have h₃ : R c a := by
        rw [h₀]
        apply trans h₁
        rw [h₂]
        apply refl
      -- dually, if a=d then b = a ∨ b = d ∨ b = d:
      have h₀ : b = (l.sup a b) := by
        apply l.le_antisymm
        · apply l.le_sup_right
        apply l.sup_le
        · exact o₀
        · apply l.le_refl
      have h₁ : R (l.sup a b) (l.sup d b) := by
        apply conJoin
        exact h
        apply refl
      have h₂ : (l.sup d b) = d := by
        apply l.le_antisymm
        apply l.sup_le
        apply l.le_refl
        apply l.le_trans
        exact o₁
        exact o₂
        apply l.le_sup_left
      have h₃ : R b d := by
        rw [h₀]
        apply trans h₁
        rw [h₂]
        apply refl
      -- so... b = d = a = c !
      apply trans
      · exact h₃
      · apply trans
        · apply symm
          exact h
        · apply symm
          tauto

local notation x "∧" y => N₅.inf x y
local notation x "∨" y => N₅.sup x y

/-- Any congruence of `N₅` with `3∼0` makes `2∼4`. -/
lemma of₃₀ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence N₅ R) (H : R 3 0) :
    R 2 4 := by
      let refl := hR₀.1.1.1.refl
      let symm := hR₀.1.2.symm
      let conJoin := hR₀.2.1
      let conMeet := hR₀.2.2
      have h₀ : 4 = (4 ∧ 0) := by decide
      have h₁ : R (4 ∧ 0) (4 ∧ 3) := by
        apply symm
        exact conMeet 4 4 3 0 (refl 4) H
      have : (4 ∧ 3) = 1 := by decide
      have : R 4 1 := by
        rw [h₀]
        rw [this] at h₁
        exact h₁
      rw [show 2 = (2 ∨ 1) by decide]
      rw [show 4 = (2 ∨ 4) by decide]
      apply conJoin
      · apply refl
      · apply symm
        tauto
/-- Any congruence of `N₅` with `3∼2` makes `2∼4`. -/
lemma of₃₂ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence N₅ R) (H : R 3 2) :
    R 2 4 := by
  let refl := hR₀.1.1.1.refl
  let symm := hR₀.1.2.symm
  let conJoin := hR₀.2.1
  let conMeet := hR₀.2.2
  have h₀ : R (3 ∨ 3) (3 ∨ 2) := by apply conJoin;apply refl;exact H
  have h₁ : (3 ∨ 3) = 3 := by decide
  have h₂ : R 3 (3 ∨ 2) := by nth_rw 1 [← h₁];exact h₀
  have h₃ : (3 ∨ 2) = 0 := by decide
  have : R 3 0 := by rw [h₃] at h₂;exact h₂
  apply of₃₀ <;> tauto
lemma of₃₄ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence N₅ R) (H : R 3 4) : R 2 4 := by
  let refl := hR₀.1.1.1.refl
  let symm := hR₀.1.2.symm
  let conJoin := hR₀.2.1
  let conMeet := hR₀.2.2
  have h₀ : R (3 ∨ 3) (3 ∨ 4) := by apply conJoin;apply refl;exact H
  have h₁ : (3 ∨ 3) = 3 := by decide
  have h₂ : R 3 (3 ∨ 2) := by nth_rw 1 [← h₁];exact h₀
  have h₃ : (3 ∨ 2) = 0 := by decide
  have : R 3 0 := by rw [h₃] at h₂;exact h₂
  apply of₃₀ <;> tauto

/-- Any congruence of `N₅` with `3∼1` makes `2∼4`. -/
lemma of₃₁ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence N₅ R) (H : R 3 1) :
    R 2 4 := by
  let refl := hR₀.1.1.1.refl
  let symm := hR₀.1.2.symm
  let trans := fun {a b c} => hR₀.1.1.2.trans a b c
  let conJoin := hR₀.2.1
  let conMeet := hR₀.2.2
  have h₀ : R (3 ∨ 2) (1 ∨ 2) := by apply conJoin;exact H;apply refl
  have h₁ : (3 ∨ 2) = 0 := by decide
  have h₂ : R 0 (1 ∨ 2) := by nth_rw 1 [← h₁];exact h₀
  have h₃ : (1 ∨ 2) = 2 := by decide
  have : R 0 2 := by rw [h₃] at h₂;exact h₂
  -- then R 2 4 because 2 = 4 ∧ 2 ∼ 4 ∧ 0 = 4:
  have : (4 ∧ 2) = 2 := by decide
  rw [← this]
  have : R (4 ∧ 2) (4 ∧ 0) := by apply conMeet;apply refl;tauto
  apply trans this
  apply refl

/-- Any congruence of `N₅` with `2∼1` makes `2∼4`. -/
lemma of₂₁ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence N₅ R) (H : R 2 1) : R 2 4 := by
  let refl := hR₀.1.1.1.refl; let symm := hR₀.1.2.symm;
  let trans := fun {a b c} => hR₀.1.1.2.trans a b c
  let conJoin := hR₀.2.1; let conMeet := hR₀.2.2
  -- if 2=1 then 3 = 3 ∨ 1 = 3 ∨ 2 = 0
  have g₀ : 3 = (3 ∨ 1) := by decide
  have h₀ : R (3 ∨ 1) (3 ∨ 2) := by apply conJoin;apply refl;apply symm;exact H
  have g₁ : (3 ∨ 2) = 0 := by decide
  apply of₃₀ hR₀
  rw [g₀]
  apply trans h₀
  rw [g₁]
  apply refl

/-- Any congruence of `N₅` with `4∼0` makes `2∼4`. -/
lemma of₄₀ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence N₅ R) (H : R 4 0) : R 2 4 := by
  let refl := hR₀.1.1.1.refl; let symm := hR₀.1.2.symm;
  let trans := fun {a b c} => hR₀.1.1.2.trans a b c
  let conJoin := hR₀.2.1; let conMeet := hR₀.2.2
  -- dual to of₂₁:
  have g₀ : 3 = (3 ∧ 0) := by decide
  have h₀ : R (3 ∧ 0) (3 ∧ 4) := by apply conMeet;apply refl;apply symm;exact H
  have g₁ : (3 ∧ 4) = 1 := by decide
  apply of₃₁ hR₀
  rw [g₀]
  apply trans h₀
  rw [g₁]
  apply refl

/-- Any congruence of `N₅` with `3` equivalent to something else
 makes `2∼4`. -/
lemma of₃ (R : Fin 5 → Fin 5 → Prop) (hR₀ : congruence N₅ R)
  (H : ∃ i, (i ≠ 3) ∧ R 3 i) : R 2 4 := by
      obtain ⟨i,hi⟩ := H
      fin_cases i
      · simp at hi
        apply of₃₀ hR₀ hi
      · simp at hi
        apply of₃₁ hR₀ hi
      · simp at hi
        apply of₃₂ hR₀ hi
      · simp at hi
      · simp at hi
        apply of₃₄ hR₀ hi

/-- The lattice `N₅` is subdirectly irreducible. -/
theorem sdi_N₅ : SubdirectlyIrreducible N₅ := by
    right
    use 2, 4
    constructor
    · simp
    intro R hR₀ hR₁
    let refl := hR₀.1.1.1.refl
    let symm := fun {a b} => hR₀.1.2.symm a b
    let conJoin := hR₀.2.1
    let conMeet := hR₀.2.2
    by_cases H : ∃ i ≠ 3, R 3 i
    · apply of₃ <;> tauto
    · by_contra H'
      apply hR₁
      ext i j
      fin_cases i
      · simp
        fin_cases j
        · simp;tauto
        · simp
          contrapose! H'
          apply ofIcc hR₀ (show 1 ∣ 2 by simp) (show 2 ∣ 4 by simp) (show 4 ∣ 0 by simp) (symm H')
        · simp
          contrapose! H'
          apply ofIcc hR₀ (by change 2 ∣ 2;simp) ((by change 2 ∣ 4;simp))
            (by change 4 ∣ 0;simp) (symm H')
        · simp
          contrapose! H
          use 0
          simp
          apply symm H
        · simp
          contrapose! H'
          apply of₄₀ hR₀
          apply symm H'
      · simp
        fin_cases j
        · simp
          contrapose! H'
          apply ofIcc hR₀ (by change 1 ∣ 2;simp) ((by change 2 ∣ 4;simp)) (by change 4 ∣ 0;simp) H'
        · simp;tauto
        · simp
          contrapose! H'
          apply of₂₁ hR₀ <|symm H'
        · simp
          contrapose! H
          use 1
          simp
          apply symm H
        · simp
          contrapose! H'
          apply ofIcc hR₀ (by change 1 ∣ 2;simp) ((by change 2 ∣ 4;simp)) (by change 4 ∣ 4;simp) H'
      · simp
        fin_cases j
        · simp
          contrapose! H'
          apply ofIcc hR₀ (by change 2 ∣ 2;simp) ((by change 2 ∣ 4;simp)) (by change 4 ∣ 0;simp) H'
        · simp
          contrapose! H'
          apply of₂₁ hR₀ H'
        · simp;tauto
        · simp
          contrapose! H
          use 2
          simp
          apply symm H
        · simp
          exact H'
      · simp
        constructor
        · intro h
          contrapose! H
          use j
          constructor
          · contrapose! H
            exact H.symm
          · tauto
        · intro h
          symm at h
          subst h
          tauto
      · simp
        fin_cases j
        · simp
          contrapose! H'
          apply of₄₀ hR₀ H'
        · simp
          contrapose! H'
          apply ofIcc hR₀ (by change 1 ∣ 2;simp) ((by change 2 ∣ 4;simp))
            (by change 4 ∣ 4;simp) <|symm H'
        · simp
          contrapose! H'
          apply symm H'
        · simp
          contrapose! H'
          apply of₃₄ hR₀ <| symm H'
        · simp;tauto

/-- There exists a lattice that is subdirectly irreducible
 but not simple, namely `N₅`. -/
theorem exists_sdi_not_simple : ∃ l : Lattice (Fin 5),
  SubdirectlyIrreducible l ∧ ¬ Simple l := by
  use N₅
  constructor
  · exact sdi_N₅
  · exact not_simple_N₅

end UniversalAlgebra
