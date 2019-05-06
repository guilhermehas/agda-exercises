import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm; *-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.Relations using (_<_; z<s; s<s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning

eq² : ∀ {m} → suc (m + suc (m + zero)) ≡ m + suc (m + zero) + 1
eq² {m} = 
  begin
    suc (m + suc (m + zero))
   ≡⟨ +-comm 1 (m + suc (m + zero)) ⟩
     m + suc (m + zero) + 1
   ∎

eq¹ : ∀ {m} → suc (m + suc (m + zero))  ≡ m + suc (suc (m + zero))
eq¹ {m} = 
  begin
    suc (m + suc (m + zero))
  ≡⟨ +-comm 1 (m + suc (m + zero)) ⟩
    m + suc (m + zero) + 1
  ≡⟨ +-assoc m (suc (m + zero)) 1 ⟩
    m + suc (m + zero + 1)
  ≡⟨ cong (λ x → m + suc x) (+-comm (m + zero) 1) ⟩
    m + suc (suc (m + zero))
   ∎

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)


∃-even : ∀ {n : ℕ} → ∃[ m ] ( 2 * m  ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] ( 2 * m + 1  ≡ n) → odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc zero , refl ⟩ = even-suc (odd-suc even-zero)
∃-even ⟨ suc (suc m) , refl ⟩ = even-suc (odd-suc (∃-even ⟨ suc m , {!eq¹ {m}!} ⟩))

∃-odd ⟨ zero , refl ⟩ = odd-suc even-zero
∃-odd ⟨ suc m , refl ⟩ = {!!}
