import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Sublattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Order.Lattice
import Mathlib.Order.Filter.Defs
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

lemma Fin.lcm.proof {n : ℕ} {a b : Fin n} (h : ¬a.1.lcm b.1 < n) : 0 < n := by
    by_cases H : n = 0
    · have := a.2
      subst H
      simp at this
    · omega

lemma Fin.gcd.proof {n : ℕ} {a b : Fin n} : a.1.gcd b.1 < n := by
    by_cases H₀ : n = 0
    · have := a.2
      subst H₀
      simp at this
    · by_cases H₁ : n = 1
      · subst H₁
        rw [fin_one_eq_zero a, fin_one_eq_zero b]
        decide
      · by_cases H₂ : a.1 = 0
        · rw [H₂]
          simp
        · have : a.1.gcd b.1 ≤ a.1 := by
            refine Nat.gcd_le_left b ?_
            omega
          omega

/-- Fin.lcm on Fin n is 0 if Nat.lcm is not in Fin n. -/
def Fin.lcm {n : ℕ} (a b : Fin n) : Fin n :=
    dite (a.1.lcm b.1 < n) (fun h => ⟨a.1.lcm b.1, h⟩)
                           (fun h => ⟨0, Fin.lcm.proof h⟩)

/-- The gcd on ℕ works without modification on Fin n. -/
def Fin.gcd {n : ℕ} (a b : Fin n) : Fin n := ⟨a.1.gcd b.1, Fin.gcd.proof⟩

theorem D.sup_le (n : ℕ) (a b c : Fin n) (h₀ : a.1.lcm b ∣ c) (g₀ : c.1 ≠ 0) :
    a.1.lcm b ≤ c := by
  obtain ⟨d,hd⟩ := h₀
  rw [hd]
  by_cases H : d = 0
  · subst H
    simp at hd
    tauto
  · have : a.1.lcm b.1 = (a.1.lcm b.1) * 1 := by simp
    nth_rw 1 [this]
    have : 1 ≤ d := by omega
    exact Nat.mul_le_mul_left (a.1.lcm b) this

/-- Fin n as a partial divisor lattice. -/
noncomputable def D (n : ℕ) : Lattice (Fin n) := {
    le := fun x y =>
        Dvd.dvd x.1 y.1 -- x.1 ∣ y.1
    lt := fun x y => Dvd.dvd x.1 y.1 ∧ ¬ Dvd.dvd y.1 x.1
    le_refl := fun a => dvd_refl a.1
    le_antisymm := fun a b h₀ h₁ => Fin.eq_of_val_eq <| Nat.dvd_antisymm h₀ h₁
    sup := Fin.lcm
    inf := Fin.gcd
    le_trans := fun a b c h₀ h₁ => Nat.dvd_trans h₀ h₁
    le_sup_left := fun a b => by
        unfold Fin.lcm
        split_ifs with g₀
        · exact Nat.dvd_lcm_left a b
        · exact dvd_zero _
    le_sup_right := fun a b => by
        unfold Fin.lcm
        split_ifs with g₀
        · exact Nat.dvd_lcm_right a b
        · exact dvd_zero _
    sup_le := fun a b c h₀ h₁ => by
        simp [Fin.lcm]
        split_ifs with g₀
        · exact Nat.lcm_dvd h₀ h₁
        · simp
          have := Nat.lcm_dvd h₀ h₁
          contrapose! g₀
          have : a.1.lcm b ≤ c := by apply D.sup_le <;> tauto
          calc _ ≤ c.1 := this
               _ < _ := c.2
    inf_le_left := fun a b => Nat.gcd_dvd_left a.1 b.1
    inf_le_right := fun a b => Nat.gcd_dvd_right a.1 b.1
    le_inf := fun _ _ _ => Nat.dvd_gcd
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
            | inl h₂ => exact .inl <| h.trans h₂
            | inr h₂ =>
              subst h
              tauto
          | inr h =>
            cases h₁ with
            | inl h => subst h; tauto
            | inr h₂ =>
              have ha : a = x ∨ a = y := by rw [Set.pair_eq_pair_iff] at h; tauto
              have hb : b = x ∨ b = y := by rw [Set.pair_eq_pair_iff] at h; tauto
              cases ha with
              | inl h =>
                subst h
                cases hb with
                | inl h => subst h; tauto
                | inr h =>
                  subst h
                  rw [Set.ext_iff] at h₂
                  specialize h₂ a
                  simp at h₂
                  tauto
              | inr h =>
                symm at h
                subst h
                cases hb with
                | inl h =>
                  subst h
                  rw [← h₂, Set.ext_iff] at h
                  specialize h c
                  simp at h
                  cases h with
                  | inl h => tauto
                  | inr h =>
                    subst h
                    rw [Set.pair_comm]
                    tauto
                | inr h => subst h; tauto
        symm := fun a b h => by
            cases h with
            | inl h => subst h;tauto
            | inr h => right;rw [← h];rw [Set.pair_eq_pair_iff];simp}

/-- An interval `[x,y]` is *indiscernible* if its elements `u` agree on
whether they are above or below a given element `z ∉ [x,y]`.
The equivalence relation formed by collapsing such an interval
preserves `∨`.
-/
theorem preserve_sup_of_indiscernible {A : Type*} (l : Lattice A) (x y : A)
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
    | inl h => tauto
    | inr h =>
      rw [Set.pair_subset_iff] at h
      by_cases H : x₀ ≤ y
      · rw [Set.pair_subset_iff]
        exact .inr ⟨⟨le_trans h.1.1 le_sup_right, sup_le H h.1.2⟩,
               ⟨le_trans h.2.1 le_sup_right, sup_le H h.2.2⟩⟩
      · left
        have hxy₀ := hxy' (SemilatticeSup.sup x₀ y₁) (by
          simp only [Set.Icc, Set.mem_setOf_eq]
          contrapose! H
          apply le_trans le_sup_left H.2) y₀ h.1 y₁ h.2
        have hxy₁ := hxy' (SemilatticeSup.sup x₀ y₀) (by
          simp only [Set.Icc, Set.mem_setOf_eq]
          contrapose! H
          apply le_trans le_sup_left H.2) y₀ h.1 y₁ h.2
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
        exact ⟨⟨le_trans h.1.1 le_sup_left, sup_le h.1.2 H.2⟩,
               ⟨le_trans h.2.1 le_sup_left, sup_le h.2.2 H.2⟩⟩
      · by_cases H₀ : x ≤ y₀
        · have h₀ := hxy' (SemilatticeSup.sup x₁ y₀) (by
                contrapose! H
                exact ⟨H₀, le_trans le_sup_right H.2⟩) x₀ (by apply h;simp) x₁ (by apply h;simp)
          have h₁ := hxy' (SemilatticeSup.sup x₀ y₀) (by
                contrapose! H
                exact ⟨H₀, le_trans le_sup_right H.2⟩) x₀ (by apply h;simp) x₁ (by apply h;simp)
          left
          apply le_antisymm
          · apply sup_le (h₀.1.mpr le_sup_left) le_sup_right
          · apply sup_le (h₁.1.mp  le_sup_left) le_sup_right
        · by_cases H₁ : y₀ ≤ y
          · rw [Set.pair_subset_iff] at h ⊢
            exact .inr ⟨⟨le_trans h.1.1 le_sup_left, sup_le h.1.2 H₁⟩,
                        ⟨le_trans h.2.1 le_sup_left, sup_le h.2.2 H₁⟩⟩
          left
          apply le_antisymm
          · apply sup_le
            · have := hxy' (SemilatticeSup.sup x₁ y₀) (by
                    contrapose! H₁
                    apply le_trans le_sup_right H₁.2) x₀ (by apply h;simp) x₁ (by apply h;simp)
              apply this.1.mpr le_sup_left
            · apply le_sup_right

          · apply sup_le
            · have := hxy' (SemilatticeSup.sup x₀ y₀) (by
                    contrapose! H₁
                    apply le_trans le_sup_right H₁.2) x₀ (by apply h;simp) x₁ (by apply h;simp)
              apply this.1.mp le_sup_left
            · apply le_sup_right
    | inr h' =>
      rw [Set.pair_subset_iff] at h h' ⊢
      exact .inr ⟨⟨le_trans h.1.1 le_sup_left, sup_le h.1.2 h'.1.2⟩,
                  ⟨le_trans h.2.1 le_sup_left, sup_le h.2.2 h'.2.2⟩⟩


/-- Simple implies subdirectly irreducible.
((D 5) is an example of the failure of the converse.)
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

lemma N₅omega {n : ℕ} {u : Fin (n + 5)} {c₀ c₁ : ℕ} (hc₀ : ↑u = 2 * c₀) (hc₁ : 4 = ↑u * c₁) :
    u = 2 ∨ u = 4 := by
      suffices (u.1 = 2) ∨ (u.1 = 4) by
        cases this with
        | inl h => left;exact Fin.eq_of_val_eq h
        | inr h => right;exact Fin.eq_of_val_eq h
      rw [hc₀] at hc₁
      have : 2 * 2 = 2 * (c₀ * c₁) := by rw [← mul_assoc];omega
      have h₀ : 2 = c₀ * c₁ := by
        have := (mul_left_cancel_iff_of_pos (show 0 < 2 by simp) (c:= 2)
          (b := c₀ * c₁)).mp this.symm
        omega
      have : c₀ ≠ 0 := by
        intro hc
        subst hc
        simp at this
      have : c₀ ∣ 2 := Dvd.intro c₁ h₀.symm
      have : c₀ ≤ 2 := by apply Nat.le_of_dvd;simp;tauto
      have : c₀ = 1 ∨ c₀ = 2 := by omega
      cases this with
      | inl h =>
      subst h
      have : c₁ = 2 := by omega
      subst this
      tauto
      | inr h =>
          subst h
          have : c₁ = 1 := by omega
          subst this
          rw [hc₀]
          simp

lemma N₅helper {n : ℕ} : {u : Fin (n + 5) | 2 ∣ u.1 ∧ u.1 ∣ 4} = {2, 4} := by
    ext u
    constructor
    · intro ⟨⟨c₀,hc₀⟩,⟨c₁,hc₁⟩⟩
      apply N₅omega <;> tauto
    · intro h
      cases h with
      | inl h => subst h; change 2 ∣ 2 ∧ 2 ∣ _; omega
      | inr h => subst h; change 2 ∣ 4 ∧ 4 ∣ _; omega


theorem D₅_congr_sup_case_general {n : ℕ} {x₀ y₀ : Fin (n + 5)}
    (h : y₀ ∈ ({2, 4} : Set (Fin (n + 5))))
    (H : x₀ ∈ ({2, 4} : Set (Fin (n + 5)))) :
    (D (n + 5)).sup x₀ y₀ ∈ ({2, 4} : Set (Fin (n + 5))) := by
                cases H with
              | inl h =>
                subst h
                cases h with
                |inl h =>
                    subst h; left
                    exact @sup_idem (Fin (n + 5)) (D (n + 5)).toSemilatticeSup 2
                |inr h =>
                    subst h; right
                    exact (@sup_eq_right (Fin (n + 5)) (D (n + 5)).toSemilatticeSup 2 4).mpr
                        (by change 2 ∣ 4;simp)
              | inr h =>
                subst h
                cases h with
                |inl h =>
                    subst h; right
                    exact (@sup_eq_left (Fin (n + 5)) (D (n + 5)).toSemilatticeSup 4 2).mpr
                        (by change 2 ∣ 4;simp)
                |inr h =>
                    subst h
                    right
                    exact @sup_idem (Fin (n + 5)) (D (n + 5)).toSemilatticeSup 4

lemma D_zero_max {n : ℕ} (x : Fin (n + 1)) :
    (D (n+1)).sup 0 x = 0 := by
  unfold D
  unfold SemilatticeSup.sup
  simp [Fin.lcm]


open Classical in
lemma D₅_congr_sup (x₀ x₁ y₀ y₁ : Fin 5) :
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) x₀ x₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) y₀ y₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4})
      ((D 5).sup x₀ y₀) ((D 5).sup x₁ y₁) := by
      intro h₀ h₁
      rw [N₅helper] at h₀ h₁
      cases h₀ with
      | inl h =>
        subst h
        cases h₁ with
        | inl h =>
            subst h; tauto
        | inr h =>
            by_cases H : x₀ ∈ ({2, 4} : Set (Fin 5))
            · right
              rw [N₅helper]
              rw [Set.pair_subset_iff] at h ⊢
              constructor
              · apply D₅_congr_sup_case_general
                · exact h.1
                · exact H
              · apply D₅_congr_sup_case_general
                · exact h.2
                · exact H
            · rw [Set.pair_subset_iff] at h
              simp at h H
              cases h.1 with
              | inl h =>
                subst h
                cases h.2 with
                | inl h => subst h; tauto
                | inr h =>
                    subst h
                    fin_cases x₀; all_goals (try simp at H ⊢; try decide)
                    · rw [N₅helper, Set.pair_subset_iff]; decide
              | inr h =>
                subst h
                cases h.2 with
                | inl h =>
                    subst h
                    fin_cases x₀; all_goals (simp at H ⊢; try decide)
                    · rw [N₅helper, Set.pair_subset_iff]; decide
                | inr h => subst h; tauto
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
                · change (D 5).le 2 _
                  apply (D 5).le_trans
                  · change (D 5).le 2 x₀
                    rcases h.1 with (h | h) <;> (subst h;change 2 ∣ _;simp)
                  apply (D 5).le_sup_left
                · change (D 5).le ((D 5).sup x₀ y₀) 4
                  apply (D 5).sup_le
                  · rcases h.1 with (h | h) <;> (subst h;change _ ∣ 4;simp)
                  exact H
              · simp
                constructor
                · change (D 5).le 2 _
                  apply (D 5).le_trans
                  · change (D 5).le 2 x₁
                    rcases h.2 with (h | h) <;> (subst h;change 2 ∣ _;simp)
                  apply (D 5).le_sup_left
                · change (D 5).le ((D 5).sup x₁ y₀) 4
                  apply (D 5).sup_le
                  · rcases h.2 with (h | h) <;> (subst h;change _ ∣ 4;simp)
                  exact H
            · left
              change (D 5).sup x₀ y₀ = (D 5).sup x₁ y₀
              have g₀: (D 5).sup x₀ y₀ = 0 := by
                fin_cases y₀; all_goals simp at H ⊢
                · unfold D
                  unfold SemilatticeSup.sup
                  simp [Fin.lcm]
                · rcases h.1 with (h | h) <;> (subst h;decide)
              have g₁: (D 5).sup x₁ y₀ = 0 := by
                fin_cases y₀; all_goals simp at H ⊢
                · unfold D
                  unfold SemilatticeSup.sup
                  simp [Fin.lcm]
                · rcases h.2 with (h | h) <;> (subst h;decide)
              exact g₀.trans g₁.symm
        | inr h' =>
          right
          rw [Set.pair_subset_iff] at h' ⊢
          rw [N₅helper]
          constructor
          · exact D₅_congr_sup_case_general h'.1 h.1
          · exact D₅_congr_sup_case_general h'.2 h.2

open Classical in
/-- The principal equivalence relation with block `{2,4}`
preserves `∧` in `(D 5)`. -/
lemma D₅_congr_inf (x₀ x₁ y₀ y₁ : Fin 5) :
  (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) x₀ x₁ →
    (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}) y₀ y₁ →
      (fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4})
      ((D 5).inf x₀ y₀) ((D 5).inf x₁ y₁) := by
      intro h₀ h₁
      rw [N₅helper] at h₀ h₁
      cases h₀ with
      | inl h =>
        subst h
        cases h₁ with
        | inl h =>
            subst h; tauto
        | inr h =>
            by_cases H : x₀ ∈ ({2, 4} : Set (Fin 5))
            · right
              rw [N₅helper]
              rw [Set.pair_subset_iff] at h ⊢
              constructor
              · rcases H with (h | h) <;> (
                subst h
                rcases h.1 with (h | h) <;> (subst h;simp;decide))
              · rcases H with (h | h) <;> (
                subst h
                rcases h.2 with (h | h) <;> (subst h;simp;decide))
            · rw [Set.pair_subset_iff] at h
              simp at h H
              rcases h.1 with (h | h)
              all_goals (subst h; rcases h.2 with (h | h))
              all_goals subst h
              any_goals tauto
              all_goals (
                fin_cases x₀; all_goals (simp at H ⊢; try decide)
                rw [N₅helper, Set.pair_subset_iff]
                decide)
      | inr h =>
        rw [Set.pair_subset_iff] at h
        cases h₁ with
        | inl h =>
            subst h
            by_cases H : 2 ∣ y₀.1
            · right
              rw [Set.pair_subset_iff]
              constructor
              · constructor
                · change (D 5).le 2 ((D 5).inf x₀ y₀)
                  apply (D 5).le_inf
                  · rcases h.1 with (h | h) <;> (subst h;change 2 ∣ _;simp)
                  change 2 ∣ y₀.1
                  exact H
                · change (D 5).le ((D 5).inf x₀ y₀) 4
                  apply (D 5).le_trans
                  · change (D 5).le _ x₀
                    rcases h.1 with (h | h) <;> (subst h;apply (D 5).inf_le_left)
                  · change (D 5).le _ _
                    rcases h.1 with (h | h) <;> (subst h;change _ ∣ 4;simp)
              · constructor
                · change (D 5).le 2 _
                  apply (D 5).le_inf
                  · rcases h.2 with (h | h) <;> (subst h;change 2 ∣ _;simp)
                  exact H
                · change (D 5).le ((D 5).inf x₁ y₀) 4
                  apply (D 5).le_trans
                  · apply (D 5).inf_le_left
                  · rcases h.2 with (h | h) <;> (subst h;change _ ∣ 4;decide)
            · left
              change (D 5).inf x₀ y₀ = (D 5).inf x₁ y₀
              have g₀: (D 5).inf x₀ y₀ = 1 := by
                fin_cases y₀; all_goals simp at H ⊢
                · fin_cases x₀ <;> decide
                · rcases h.1 with (h | h) <;> (subst h;decide)
              have g₁: (D 5).inf x₁ y₀ = 1 := by
                fin_cases y₀; all_goals simp at H ⊢
                · fin_cases x₁ <;> decide
                · rcases h.2 with (h | h) <;> (subst h;decide)
              exact g₀.trans g₁.symm
        | inr h' =>
          right
          rw [Set.pair_subset_iff] at h' ⊢
          rw [N₅helper]
          constructor
          · rcases h.1 with (h | h) <;> (
              subst h
              rcases h'.1 with (h | h) <;> (subst h; decide))
          · rcases h.2 with (h | h) <;> (
              subst h
              rcases h'.2 with (h | h) <;> (subst h; decide))

/-- The interval `[2,4]` in `(D 5)` is indiscernible. -/
lemma N₅indiscernibleInterval (z : Fin 5) :
  z ∉ {u | 2 ∣ u.1 ∧ u.1 ∣ 4} →
    ∀ w₀ ∈ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
    ∀ w₁ ∈ {u : Fin 5 | 2 ∣ u.1 ∧ u.1 ∣ 4},
      (w₀.1 ∣ z ↔ w₁.1 ∣ z) ∧ (z.1 ∣ w₀ ↔ z.1 ∣ w₁) := by
    rw [N₅helper]
    intro hz w₀ hw₀ w₁ hw₁
    simp at hz hw₀ hw₁
    fin_cases z
    all_goals (simp at hz ⊢; try omega)
    rcases hw₀ with (h | h) <;> (
      subst h
      rcases hw₁ with (h | h) <;> (subst h; simp))

open Classical in
/-- The lattice `(D 5)` is not simple. -/
theorem not_simple_D₅ : ¬ Simple (D 5) := by
  have hio := @preserve_sup_of_indiscernible (Fin 5) (D 5) 2 4
  unfold Simple
  push_neg
  use fun a b ↦ a = b ∨ {a, b} ⊆ {x | 2 ∣ x.1 ∧ x.1 ∣ 4}
  constructor
  · constructor
    · rw [N₅helper]
      convert principalEquiv (2:Fin 5) 4 (by simp) using 1
      ext i j
      rw [Set.pair_subset_iff, Set.pair_eq_pair_iff]
      simp
      specialize hio N₅indiscernibleInterval -- speed up aesop?
      constructor <;> aesop
    · exact ⟨D₅_congr_sup, D₅_congr_inf⟩
  constructor
  · intro hc
    rw [funext_iff] at hc; specialize hc 2
    rw [funext_iff] at hc; specialize hc 4
    simp at hc
    apply hc
    rw [Set.pair_subset_iff]
    simp
  · intro hc
    rw [funext_iff] at hc; specialize hc 0
    rw [funext_iff] at hc; specialize hc 1
    simp at hc
    simpa using hc (show 0 ∈ {0,1} by simp)

/-- If `R` is a congruence of a lattice `L`
 then its blocks are convex: if
 `a ≤ b ≤ c ≤ d` and `R(a,d)` then `R(b,c)`. -/
lemma ofIcc {A : Type*} {l : Lattice A} {R : A → A → Prop}
    (hR₀ : congruence l R)
    {a b c d : A} (o₀ : l.le a b) (o₁ : l.le b c) (o₂ : l.le c d)
    (h : R a d) : R b c := by
      let refl := fun {a} => hR₀.1.1.1.refl a
      let symm := fun {a b} => hR₀.1.2.symm a b
      let conJoin := fun {a b c d} => hR₀.2.1 a b c d
      let conMeet := fun {a b c d} => hR₀.2.2 a b c d
      let trans := fun {a b c} => hR₀.1.1.2.trans a b c -- if a=d then c = d ∧ c = a ∧ c = a:
      have h₀ : c = (l.inf d c) := by
        apply l.le_antisymm
        apply l.le_inf _ _ _ o₂
        apply l.le_refl
        apply l.inf_le_right
      have h₁ : R (l.inf d c) (l.inf a c) := by
        apply conMeet (symm h) refl
      have h₂ : (l.inf a c) = a := by
        apply l.le_antisymm
        · apply l.inf_le_left
        · apply l.le_inf
          · apply l.le_refl
          · apply l.le_trans _ _ _ o₀ o₁
      have h₃ : R c a := by
        rw [h₀]
        apply trans h₁
        rw [h₂]
        apply refl -- dually, if a=d then b = a ∨ b = d ∨ b = d:
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
        apply l.le_trans _ _ _ o₁ o₂
        apply l.le_sup_left
      have h₄ : R b d := by
        rw [h₀]
        apply trans h₁
        rw [h₂]
        apply refl -- so... b = d = a = c !
      apply trans h₄ <| trans (symm h) (symm h₃)


/-- Any congruence of `(D 5)` with `3∼0` makes `2∼4`. -/
lemma of₃₀D₅ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence (D 5) R) (H : R 3 0) :
    R 2 4 := by
      let refl := hR₀.1.1.1.refl
      let symm := fun {a b} => hR₀.1.2.symm a b
      let conJoin := fun {a b c d} => hR₀.2.1 a b c d
      let conMeet := hR₀.2.2
      have h₀ : 4 = (D 5).inf 4 0 := by decide
      have h₁ : R ((D 5).inf 4 0) ((D 5).inf 4 3) := by
        apply symm
        exact conMeet 4 4 3 0 (refl 4) H
      have : ((D 5).inf 4 3) = 1 := by decide
      have : R 4 1 := by
        rw [h₀]
        rw [this] at h₁
        exact h₁
      rw [show 2 = ((D 5).sup 2 1) by decide]
      rw [show 4 = ((D 5).sup 2 4) by decide]
      exact conJoin (refl _) <| symm this

/-- Any congruence of `(D 5)` with `3∼2` makes `2∼4`. -/
lemma of₃₂D₅ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence (D 5) R) (H : R 3 2) :
    R 2 4 := by
  let refl := hR₀.1.1.1.refl
  let conJoin := fun {a b c d} => hR₀.2.1 a b c d
  have h₀ : R ((D 5).sup 3 3) ((D 5).sup 3 2) := by apply conJoin;apply refl;exact H
  have h₁ : (D 5).sup 3 3 = 3 := by decide
  have h₂ : R 3 ((D 5).sup 3 2) := by nth_rw 1 [← h₁];exact h₀
  have h₃ : (D 5).sup 3 2 = 0 := by decide
  have : R 3 0 := by rw [h₃] at h₂;exact h₂
  apply of₃₀D₅ <;> tauto

lemma of₃₄D₅ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence (D 5) R) (H : R 3 4) : R 2 4 := by
  let refl := hR₀.1.1.1.refl
  let conJoin := fun {a b c d} => hR₀.2.1 a b c d
  have h₀ : R ((D 5).sup 3 3) ((D 5).sup 3 4) := conJoin (refl _) H
  have h₁ : (D 5).sup 3 3 = 3 := by decide
  have h₂ : R 3 ((D 5).sup 3 2) := by nth_rw 1 [← h₁];exact h₀
  have h₃ : (D 5).sup 3 2 = 0 := by decide
  have : R 3 0 := by rw [h₃] at h₂;exact h₂
  apply of₃₀D₅ <;> tauto

/-- Any congruence of `(D 5)` with `3∼1` makes `2∼4`. -/
lemma of₃₁D₅ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence (D 5) R) (H : R 3 1) :
    R 2 4 := by
  let refl := hR₀.1.1.1.refl
  let symm := hR₀.1.2.symm
  let trans := fun {a b c} => hR₀.1.1.2.trans a b c
  let conJoin := fun {a b c d} => hR₀.2.1 a b c d
  let conMeet := hR₀.2.2
  have h₀ : R ((D 5).sup 3 2) ((D 5).sup 1 2) := by apply conJoin H;apply refl
  have h₁ : ((D 5).sup 3 2) = 0 := by decide
  have h₂ : R 0 ((D 5).sup 1 2) := by nth_rw 1 [← h₁];exact h₀
  have h₃ : ((D 5).sup 1 2) = 2 := by decide
  have : R 0 2 := by rw [h₃] at h₂;exact h₂ -- then R 2 4 because 2 = 4 ∧ 2 ∼ 4 ∧ 0 = 4:
  have : ((D 5).inf 4 2) = 2 := by decide
  rw [← this]
  have : R ((D 5).inf 4 2) ((D 5).inf 4 0) := by apply conMeet;apply refl;tauto
  apply trans this
  apply refl


/-- Any congruence of `(D 5)` with `2∼1` makes `2∼4`. -/
lemma of₂₁D₅ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence (D 5) R) (H : R 2 1) : R 2 4 := by
  let refl := hR₀.1.1.1.refl; let symm := hR₀.1.2.symm;
  let trans := fun {a b c} => hR₀.1.1.2.trans a b c
  let conJoin := hR₀.2.1; let conMeet := hR₀.2.2 -- if 2=1 then 3 = 3 ∨ 1 = 3 ∨ 2 = 0
  have g₀ : 3 = ((D 5).sup 3 1) := by decide
  have h₀ : R ((D 5).sup 3 1) ((D 5).sup 3 2) := by apply conJoin;apply refl;apply symm;exact H
  have g₁ : ((D 5).sup 3 2) = 0 := by decide
  apply of₃₀D₅ hR₀
  rw [g₀]
  apply trans h₀
  rw [g₁]
  apply refl

/-- Any congruence of `(D 5)` with `4∼0` makes `2∼4`. -/
lemma of₄₀D₅ {R : Fin 5 → Fin 5 → Prop} (hR₀ : congruence (D 5) R) (H : R 4 0) : R 2 4 := by
  let refl := hR₀.1.1.1.refl; let symm := hR₀.1.2.symm;
  let trans := fun {a b c} => hR₀.1.1.2.trans a b c
  let conJoin := hR₀.2.1; let conMeet := hR₀.2.2 -- dual to of₂₁:
  have g₀ : 3 = ((D 5).inf 3 0) := by decide
  have h₀ : R ((D 5).inf 3 0) ((D 5).inf 3 4) := by apply conMeet;apply refl;apply symm;exact H
  have g₁ : ((D 5).inf 3 4) = 1 := by decide
  apply of₃₁D₅ hR₀
  rw [g₀]
  apply trans h₀
  rw [g₁]
  apply refl


/-- Any congruence of `(D 5)` with `3` equivalent to something else
 makes `2∼4`. -/
lemma of₃D₅ (R : Fin 5 → Fin 5 → Prop) (hR₀ : congruence (D 5) R)
  (H : ∃ i ≠ 3, R 3 i) : R 2 4 := by
      obtain ⟨i,hi⟩ := H
      fin_cases i
      all_goals (simp at hi)
      · apply of₃₀D₅ hR₀ hi
      · apply of₃₁D₅ hR₀ hi
      · apply of₃₂D₅ hR₀ hi
      · apply of₃₄D₅ hR₀ hi


/-- The lattice `(D 5)` is subdirectly irreducible. -/
theorem sdi_D₅ : SubdirectlyIrreducible (D 5) := by
    have h₁₂ : (D 5).le 1 2 := by change 1 ∣ 2;simp
    have h₂₄ : (D 5).le 2 4 := by change 2 ∣ 4;simp
    have h₄₀ : (D 5).le 4 0 := by change 4 ∣ 0;simp
    have h₂₂ : (D 5).le 2 2 := by change 2 ∣ 2;simp
    have h₄₄ : (D 5).le 4 4 := by change 4 ∣ 4;simp
    right
    use 2, 4
    constructor
    · simp
    intro R hR₀ hR₁
    let refl := hR₀.1.1.1.refl
    let symm := fun {a b} => hR₀.1.2.symm a b
    by_cases H : ∃ i ≠ 3, R 3 i
    · apply of₃D₅ <;> tauto
    · by_contra H'
      apply hR₁
      ext i j
      fin_cases i; all_goals simp
      · fin_cases j
        all_goals (simp; try tauto); all_goals contrapose! H'
        · apply ofIcc hR₀ h₁₂ h₂₄ h₄₀ (symm H')
        · apply ofIcc hR₀ h₂₂ h₂₄ h₄₀ (symm H')
        · apply of₃₀D₅ hR₀ (symm H')
        · apply of₄₀D₅ hR₀ <| symm H'
      · fin_cases j
        all_goals (simp; try tauto); all_goals contrapose! H'
        · apply ofIcc hR₀ h₁₂ h₂₄ h₄₀ H'
        · apply of₂₁D₅ hR₀ <|symm H'
        · apply of₃₁D₅ hR₀ (symm H')
        · apply ofIcc hR₀ h₁₂ h₂₄ h₄₄ H'
      · fin_cases j
        all_goals (simp; try tauto); all_goals contrapose! H'
        · apply ofIcc hR₀ h₂₂ h₂₄ h₄₀ H'
        · apply of₂₁D₅ hR₀ H'
        · apply of₃₂D₅ hR₀ (symm H')
      · constructor
        · contrapose! H
          use j
          tauto
        · intro h
          rw [h]
          tauto
      · fin_cases j; all_goals (simp; try tauto); all_goals (contrapose! H')
        · apply of₄₀D₅ hR₀ H'
        · apply ofIcc hR₀ h₁₂ h₂₄ h₄₄ <|symm H'
        · apply of₃₄D₅ hR₀ <| symm H'

/-- There exists a lattice that is subdirectly irreducible
 but not simple, namely `N₅`. -/
theorem exists_sdi_not_simple : ∃ l : Lattice (Fin 5),
  SubdirectlyIrreducible l ∧ ¬ Simple l := ⟨D 5, sdi_D₅, not_simple_D₅⟩
end UniversalAlgebra

def mysetoid {A : Type*} (F : Set A) : Setoid A :=
    {
        r := fun a b => a = b ∨ {a,b} ⊆ F
        iseqv := {
            refl := fun a => .inl rfl
            trans := by
                intro a b c h₀ h₁
                rcases h₀ with (h | h)
                · rcases h₁ with (g | g)
                  · exact .inl <| h.trans g
                  · rw [h]
                    exact .inr g
                · rcases h₁ with (g | g)
                  · rw [← g]
                    exact .inr h
                  · rw [Set.pair_subset_iff] at g h ⊢
                    tauto
            symm := by
                intro a b h
                rw [Set.pair_subset_iff] at h ⊢
                tauto
        }
    }

noncomputable def freese {A : Type*} (L : Lattice A) (F : Set A)
    (hF : ∀ x ∈ F, ∀ y, x ≤ y → y ∈ F)
    (hm : ∀ x ∈ F, ∀ y ∈ F, L.inf x y ∈ F) :
    Lattice (Quotient (mysetoid F)) := {
        le := by
            intro A B
            by_cases ∃ a ∈ F, B = ⟦a⟧
            · exact True
            · exact ∃ a b, A = ⟦a⟧ ∧ B = ⟦b⟧ ∧ L.le a b
        le_refl := by
            intro A
            split_ifs with g₀
            have ⟨a,ha⟩ : ∃ a, A = ⟦a⟧ := by
                refine (Function.Surjective.exists ?_).mp ?_
                exact Quotient.mk_surjective
                use A
            use a, a
        le_trans := fun a b c => by
            split_ifs with g₀ g₁ g₂
            · trivial
            · intro _ ⟨u,v,huv⟩
              contrapose! g₁
              use v
              have : u ∈ F := by
                have {y} (hy : b = ⟦y⟧) : y ∈ F := by
                    obtain ⟨n,hn⟩ := g₀
                    have hyn := hy.symm.trans hn.2
                    simp [mysetoid] at hyn
                    rcases hyn with (h | h)
                    exact h ▸ hn.1
                    exact h (by simp)
                exact this huv.1
              exact ⟨hF _ this _ huv.2.2, huv.2.1⟩
            · intro
              trivial
            intro ⟨a',b', h'⟩ ⟨x₀, x₁, hx⟩
            use a', x₁
            constructor
            · exact h'.1
            constructor
            · exact hx.2.1
            · have : b' = x₀ := by
                have hb'x₀ := h'.2.1.symm.trans hx.1
                simp [mysetoid] at hb'x₀
                rcases hb'x₀ with (h | h)
                · exact h
                · push_neg at g₀
                  exact (g₀ x₀ (by apply h;simp) hx.1).elim
              exact h'.2.2.trans <| this ▸ hx.2.2
        le_antisymm := fun a b => by
            split_ifs with g₀ g₁ g₂
            · intros
              unfold mysetoid at a b
              obtain ⟨a₀,ha₀⟩ := g₀
              obtain ⟨b₀,hb₀⟩ := g₁
              rw [ha₀.2, hb₀.2]
              refine Quotient.sound' ?_
              right
              refine Set.pair_subset ?_ ?_
              · exact hb₀.1
              · exact ha₀.1
            · intro _ h
              sorry
            · sorry
            · sorry
        sup := by
            apply Quotient.lift₂
            · intro a₁ b₁ a₂ b₂ ha hb
              change ⟦ L.sup a₁ b₁⟧ = ⟦ L.sup a₂ b₂⟧
              apply Quot.sound
              unfold mysetoid
              simp at ha hb
              simp
              rcases ha with (ha | ha)
              · rcases hb with (hb | hb)
                · rw [ha, hb]
                  tauto
                rw [ha]
                rw [Set.pair_subset_iff] at hb ⊢
                right
                constructor
                · apply hF
                  · exact hb.1
                  · apply le_sup_right
                · apply hF
                  · exact hb.2
                  · apply le_sup_right
              rcases hb with (hb | hb)
              · rw [hb]
                right
                rw [Set.pair_subset_iff] at ha ⊢
                constructor
                · apply hF
                  · exact ha.1
                  · apply le_sup_left
                · apply hF
                  · exact ha.2
                  · apply le_sup_left
              right
              rw [Set.pair_subset_iff] at ha ⊢
              constructor
              · apply hF
                · exact ha.1
                · apply le_sup_left
              · apply hF
                · exact ha.2
                · apply le_sup_left
        sup_le := by sorry
        le_sup_right := by sorry
        le_sup_left := by sorry
        inf := by
            apply Quotient.lift₂
            · let f (a b : A) : Quotient (mysetoid F) := by
                by_cases Ha : a ∈ F
                by_cases Hb : b ∈ F
                · exact ⟦a⟧ -- L.inf a b
                · exact ⟦b⟧
                by_cases Hb : b ∈ F
                · exact ⟦a⟧
                · exact ⟦L.inf a b⟧
              intro a₁ b₁ a₂ b₂ ha hb
              change
                 f a₁ b₁ = f a₂ b₂
              simp [f]
              simp [mysetoid] at ha hb
              split_ifs with g₀ g₁ g₂ g₃
              all_goals apply Quot.sound
              all_goals try simp [mysetoid]
              · tauto
              · rcases ha with (ha|ha)
                rcases hb with (hb|hb)
                rw [hb] at g₁
                tauto
                right
                rw [Set.pair_subset_iff]
                constructor
                tauto
                apply hb
                simp
                rcases hb with (hb|hb)
                rw [hb] at g₁
                tauto
                right
                rw [Set.pair_subset_iff] at ha hb ⊢
                tauto
              · tauto
              · rcases ha with (ha | ha)
                rcases hb with (hb | hb)
                rw [hb] at g₁
                tauto
                rw [ha] at g₀
                tauto
                rw [Set.pair_subset_iff] at ha
                tauto
              · rcases hb with (hb | hb)
                rw [hb] at g₁
                tauto
                right
                rw [Set.pair_subset_iff]
                sorry
              · tauto
              · sorry
              · sorry
              · tauto
              · sorry
              · tauto
              · sorry
              · sorry
              · sorry
              · sorry
              · sorry
        inf_le_left := by sorry
        inf_le_right := by sorry
        le_inf := by sorry
    }
--     congruence L (fun a b => a = b ∨ {a,b} ⊆ F) := by
--   constructor
--   · exact {
--         refl := fun a => .inl rfl
--         trans := fun a b c h₀ h₁ => by
--             rcases h₀ with (h | h)
--             · rcases h₁ with (g | g)
--               · exact .inl <| h.trans g
--               · rw [h]
--                 exact .inr g
--             · rcases h₁ with (g | g)
--               · rw [← g]
--                 exact .inr h
--               · rw [Set.pair_subset_iff] at g h ⊢
--                 tauto
--         symm := fun a b h => by
--             rw [Set.pair_subset_iff] at h ⊢
--             tauto
--     }
--   · constructor
--     · intro x₀ x₁ y₀ y₁ h₀ h₁
--       rcases h₀ with (h | h)
--       · rcases h₁ with (g | g)
--         · rw [h, g]
--           tauto
--         · rw [h]
--           right
--           rw [Set.pair_subset_iff]
--           constructor
--           · apply hF y₀ (by apply g;simp)
--             apply L.le_sup_right
--           · apply hF y₁ (by apply g;simp)
--             apply L.le_sup_right
--       · rcases h₁ with (g | g)
--         · rw [g]
--           right
--           rw [Set.pair_subset_iff]
--           constructor
--           · apply hF x₀ (by apply h;simp)
--             apply L.le_sup_left
--           · apply hF x₁ (by apply h;simp)
--             apply L.le_sup_left
--         · right
--           rw [Set.pair_subset_iff] at g h ⊢
--           constructor
--           · apply hF x₀ (by apply h.1)
--             apply L.le_sup_left
--           · apply hF x₁ (by apply h.2)
--             apply L.le_sup_left
--     · intro x₀ x₁ y₀ y₁ h₀ h₁
--       rcases h₀ with (h | h)
--       · rcases h₁ with (g | g)
--         · rw [h, g]
--           tauto
--         · rw [h]
--           /- not true, let
--             [12]
--          [8]
--           4 [6] [9] [10]

--           2    3    [5] [7] [11]
--           1
--           -/
--           sorry
--       · rcases h₁ with (g | g)
--         · rw [g]
--           left
--           sorry
--         · right
--           rw [Set.pair_subset_iff]
--           constructor
--           · apply hm
--             · apply h
--               simp
--             · apply g
--               simp
--           · apply hm
--             · apply h
--               simp
--             · apply g
--               simp
