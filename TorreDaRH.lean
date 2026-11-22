/-
© 2026 Fortunato Zampaglione — Programma DROMIC
Passo di Eulero e torre delle lune: positività di Hankel a OGNI rango per momenti di una misura atomica positiva.
Proprietà Intellettuale e Copyright Riservato all'Autore (Fortunato Zampaglione). L'architettura teorica, il corpus documentale, i codici e i protocolli di verifica citati appartengono in via esclusiva all'Autore.
-/
import Mathlib
open Finset
namespace FortunatoZampaglione

/-- Momenti di una misura atomica: a_m = Σ_n w_n · x_n^m. -/
noncomputable def MomentoAtomico (w x : ℕ → ℝ) (m : ℕ) : ℝ := ∑' n, w n * x n ^ m

/-- Identità di Gram: la forma di Hankel (con shift ell) è una somma di quadrati pesata. -/
theorem hankel_atomico_gram (w x : ℕ → ℝ)
    (hs : ∀ m, Summable fun n => w n * x n ^ m) (N ell : ℕ) (v : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, v i * MomentoAtomico w x (i.val + j.val + ell) * v j
      = ∑' n, w n * x n ^ ell * (∑ i : Fin N, v i * x n ^ i.val) ^ 2 := by
  unfold MomentoAtomico
  have h1 : ∀ i j : Fin N, v i * (∑' n, w n * x n ^ (i.val + j.val + ell)) * v j
      = ∑' n, v i * (w n * x n ^ (i.val + j.val + ell)) * v j := by
    intro i j
    rw [← tsum_mul_left, ← tsum_mul_right]
  have hsum : ∀ i j : Fin N, Summable fun n => v i * (w n * x n ^ (i.val + j.val + ell)) * v j :=
    fun i j => ((hs _).mul_left _).mul_right _
  simp only [h1]
  have h2 : ∀ i : Fin N, ∑ j : Fin N, ∑' n, v i * (w n * x n ^ (i.val + j.val + ell)) * v j
      = ∑' n, ∑ j : Fin N, v i * (w n * x n ^ (i.val + j.val + ell)) * v j := by
    intro i
    exact (Summable.tsum_finsetSum (fun j _ => hsum i j)).symm
  simp only [h2]
  rw [← Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hsum i j))]
  congr 1
  funext n
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positività di Hankel a ogni rango e a ogni shift, per pesi ≥ 0 e nodi ≥ 0. -/
theorem hankel_atomico_nonneg (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hx : ∀ n, 0 ≤ x n)
    (hs : ∀ m, Summable fun n => w n * x n ^ m) (N ell : ℕ) (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, v i * MomentoAtomico w x (i.val + j.val + ell) * v j := by
  rw [hankel_atomico_gram w x hs N ell v]
  exact tsum_nonneg fun n => mul_nonneg (mul_nonneg (hw n) (pow_nonneg (hx n) _)) (sq_nonneg _)

/-- Localizzatore: con nodi in [0,1] la forma a shift 1 non supera quella a shift 0. -/
theorem hankel_atomico_localizzatore (w x : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hx : ∀ n, 0 ≤ x n)
    (hx1 : ∀ n, x n ≤ 1) (hs : ∀ m, Summable fun n => w n * x n ^ m) (N : ℕ) (v : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, v i * MomentoAtomico w x (i.val + j.val + 1) * v j
      ≤ ∑ i : Fin N, ∑ j : Fin N, v i * MomentoAtomico w x (i.val + j.val + 0) * v j := by
  rw [hankel_atomico_gram w x hs N 1 v, hankel_atomico_gram w x hs N 0 v]
  have hsq : ∀ n, (∑ i : Fin N, v i * x n ^ i.val) ^ 2
      = ∑ i : Fin N, ∑ j : Fin N, v i * (x n ^ (i.val + j.val)) * v j := by
    intro n
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hS : ∀ ell : ℕ, Summable fun n => w n * x n ^ ell * (∑ i : Fin N, v i * x n ^ i.val) ^ 2 := by
    intro ell
    simp only [hsq, Finset.mul_sum]
    apply summable_sum; intro i _
    apply summable_sum; intro j _
    have := ((hs (i.val + j.val + ell)).mul_left (v i)).mul_right (v j)
    refine this.congr ?_
    intro n; ring
  apply Summable.tsum_le_tsum _ (hS 1) (hS 0)
  intro n
  have h0 : 0 ≤ w n * (∑ i : Fin N, v i * x n ^ i.val) ^ 2 := mul_nonneg (hw n) (sq_nonneg _)
  have : w n * x n ^ 1 * (∑ i : Fin N, v i * x n ^ i.val) ^ 2
      = x n * (w n * (∑ i : Fin N, v i * x n ^ i.val) ^ 2) := by ring
  rw [this, pow_zero, mul_one]
  calc x n * (w n * (∑ i : Fin N, v i * x n ^ i.val) ^ 2)
      ≤ 1 * (w n * (∑ i : Fin N, v i * x n ^ i.val) ^ 2) :=
        mul_le_mul_of_nonneg_right (hx1 n) h0
    _ = _ := one_mul _

/-! ### Lo Zero (IV Romano): torre b_m = Σ_k c_k (a^k)^m, pesi di Catalan c_k > 0 -/

/-- Pesi dello Zero: coefficienti di 1 − √(1 − z), indice spostato (j = k − 1). -/
noncomputable def pesoZero (j : ℕ) : ℝ :=
  (Nat.centralBinom (j + 1) : ℝ) / ((2 * (j : ℝ) + 1) * 4 ^ (j + 1))

theorem pesoZero_nonneg (j : ℕ) : 0 ≤ pesoZero j := by
  unfold pesoZero; positivity

/-- Somma parziale dei pesi dello Zero: Σ_{j<n} c_j = 1 − C(2n,n)/4^n. -/
theorem somma_pesoZero (n : ℕ) :
    ∑ j ∈ range n, pesoZero j = 1 - (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold pesoZero
    have h := Nat.succ_mul_centralBinom_succ n
    have hR : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    have hC : (Nat.centralBinom (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
      field_simp; linarith
    rw [hC, pow_succ]
    field_simp
    ring

theorem pesoZero_summable : Summable pesoZero := by
  apply summable_of_sum_range_le (c := 1) pesoZero_nonneg
  intro n
  rw [somma_pesoZero]
  have : 0 ≤ (Nat.centralBinom n : ℝ) / 4 ^ n := by positivity
  linarith

/-- Torre dello Zero: b_m = Σ_j c_j · (a^(j+1))^m. -/
noncomputable def torreZero (a : ℝ) (m : ℕ) : ℝ :=
  MomentoAtomico pesoZero (fun j => a ^ (j + 1)) m

theorem torreZero_summable (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    Summable fun j => pesoZero j * (a ^ (j + 1)) ^ m := by
  apply Summable.of_nonneg_of_le _ _ pesoZero_summable
  · intro j; exact mul_nonneg (pesoZero_nonneg j) (pow_nonneg (pow_nonneg ha0 _) _)
  · intro j
    have h1 : (a ^ (j + 1)) ^ m ≤ 1 := pow_le_one₀ (pow_nonneg ha0 _) (pow_le_one₀ ha0 ha1)
    calc pesoZero j * (a ^ (j + 1)) ^ m ≤ pesoZero j * 1 :=
          mul_le_mul_of_nonneg_left h1 (pesoZero_nonneg j)
      _ = pesoZero j := mul_one _

/-- LO ZERO: positività di Hankel a OGNI rango e ogni shift. -/
theorem torreZero_hankel_nonneg (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (N ell : ℕ) (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, v i * torreZero a (i.val + j.val + ell) * v j :=
  hankel_atomico_nonneg pesoZero (fun j => a ^ (j + 1)) pesoZero_nonneg
    (fun j => pow_nonneg ha0 _) (torreZero_summable a ha0 ha1) N ell v

/-- LO ZERO: condizione nativa 0 ≤ vᵀH⁽¹⁾v ≤ vᵀHv a ogni rango. -/
theorem torreZero_condizione_nativa (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, v i * torreZero a (i.val + j.val + 1) * v j ∧
    ∑ i : Fin N, ∑ j : Fin N, v i * torreZero a (i.val + j.val + 1) * v j
      ≤ ∑ i : Fin N, ∑ j : Fin N, v i * torreZero a (i.val + j.val + 0) * v j :=
  ⟨torreZero_hankel_nonneg a ha0 ha1 N 1 v,
   hankel_atomico_localizzatore pesoZero (fun j => a ^ (j + 1)) pesoZero_nonneg
     (fun j => pow_nonneg ha0 _) (fun j => pow_le_one₀ ha0 ha1) (torreZero_summable a ha0 ha1) N v⟩

/-- Massa totale dello Zero: Σ c_j = 1 (da C(2n,n)/4^n → 0 non usato: qui solo ≤ 1). -/
theorem torreZero_zero_le_one (a : ℝ) : torreZero a 0 ≤ 1 := by
  unfold torreZero MomentoAtomico
  simp only [pow_zero, mul_one]
  apply pesoZero_summable.tsum_le_of_sum_range_le
  intro n
  rw [somma_pesoZero]
  have : 0 ≤ (Nat.centralBinom n : ℝ) / 4 ^ n := by positivity
  linarith

#print axioms hankel_atomico_nonneg
#print axioms hankel_atomico_localizzatore
#print axioms torreZero_hankel_nonneg
#print axioms torreZero_condizione_nativa
end FortunatoZampaglione

/-! ## Raccordo (22/11/2026): con l'Ipotesi di Riemann la torre atomica degli zeri e' positiva a ogni rango -/
namespace TorreDaRH
open FortunatoZampaglione Complex

structure NontrivialZero (s : ℂ) : Prop where
  zero : riemannZeta s = 0
  nontrivial : ¬∃ n : ℕ, s = -2 * (n + 1)
  ne_one : s ≠ 1

/-- Atomo dello zero nella carta x = 1/(4q), q = ρ(1 − ρ). -/
noncomputable def atomoC (s : ℂ) : ℂ := 1 / (4 * (s * (1 - s)))

/-- Con RH l'atomo di ogni zero e' reale e vale 1/(1 + 4γ²). -/
theorem atomo_reale (h : RiemannHypothesis) {s : ℂ} (hs : NontrivialZero s) :
    atomoC s = ((1 / (1 + 4 * s.im ^ 2) : ℝ) : ℂ) := by
  have hre : s.re = 1 / 2 := h s hs.zero hs.nontrivial hs.ne_one
  have hq : s * (1 - s) = ((1 / 4 + s.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [mul_re, sub_re, sub_im, one_re, one_im, ofReal_re, hre]; ring
    · simp only [mul_im, sub_re, sub_im, one_re, one_im, ofReal_im, hre]; ring
  have hne : (1 + 4 * s.im ^ 2 : ℝ) ≠ 0 := by positivity
  unfold atomoC
  rw [hq]
  have e : (4 : ℂ) * ((1 / 4 + s.im ^ 2 : ℝ) : ℂ) = ((1 + 4 * s.im ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, ofReal_div, ofReal_one]

/-- Con RH la parte reale dell'atomo sta in (0, 1]. -/
theorem atomo_in_zero_uno (h : RiemannHypothesis) {s : ℂ} (hs : NontrivialZero s) :
    0 ≤ (atomoC s).re ∧ (atomoC s).re ≤ 1 := by
  rw [atomo_reale h hs, ofReal_re]
  have hp : (0 : ℝ) < 1 + 4 * s.im ^ 2 := by positivity
  constructor
  · positivity
  · rw [div_le_one hp]; nlinarith [sq_nonneg s.im]

/-- TORRE DA RH: per ogni famiglia di zeri non banali con pesi non negativi, la forma di Hankel
    dei momenti atomici Σ w_n x_n^m, x_n = 1/(4 q_n), e' non negativa a ogni rango N e a ogni shift. -/
theorem torre_positiva_da_RH (h : RiemannHypothesis) (ρ : ℕ → ℂ) (hρ : ∀ n, NontrivialZero (ρ n))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hsum : ∀ m, Summable fun n => w n * (atomoC (ρ n)).re ^ m) (N ell : ℕ) (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      v i * MomentoAtomico w (fun n => (atomoC (ρ n)).re) (i.val + j.val + ell) * v j :=
  hankel_atomico_nonneg w (fun n => (atomoC (ρ n)).re) hw
    (fun n => (atomo_in_zero_uno h (hρ n)).1) hsum N ell v

/-- LOCALIZZATORE DA RH: la torre shiftata sta sotto la torre non shiftata (H¹ ≤ H⁰) a ogni rango. -/
theorem localizzatore_da_RH (h : RiemannHypothesis) (ρ : ℕ → ℂ) (hρ : ∀ n, NontrivialZero (ρ n))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hsum : ∀ m, Summable fun n => w n * (atomoC (ρ n)).re ^ m) (N : ℕ) (v : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N,
      v i * MomentoAtomico w (fun n => (atomoC (ρ n)).re) (i.val + j.val + 1) * v j
    ≤ ∑ i : Fin N, ∑ j : Fin N,
      v i * MomentoAtomico w (fun n => (atomoC (ρ n)).re) (i.val + j.val + 0) * v j :=
  hankel_atomico_localizzatore w (fun n => (atomoC (ρ n)).re) hw
    (fun n => (atomo_in_zero_uno h (hρ n)).1) (fun n => (atomo_in_zero_uno h (hρ n)).2) hsum N v

end TorreDaRH

#print axioms TorreDaRH.atomo_reale
#print axioms TorreDaRH.atomo_in_zero_uno
#print axioms TorreDaRH.torre_positiva_da_RH
#print axioms TorreDaRH.localizzatore_da_RH
