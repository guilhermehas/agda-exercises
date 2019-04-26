import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m zero p = refl
+-swap m (suc n) p =
  begin
    m + (suc n + p)
  ≡⟨⟩
    m + suc (n + p)
  ≡⟨ +-suc m (n + p) ⟩
    suc (m + (n + p))
  ≡⟨ cong suc (+-swap m n p) ⟩
    suc (n + (m + p))
  ≡⟨⟩
    suc n + (m + p)
  ∎
