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

inv : {m n : ℕ} → m ≡ n → n ≡ m
inv refl = refl

+-assoc-inv : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc-inv m n p = inv (+-assoc m n p)

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (_+_ p) (*-distrib-+ m n p) ⟩
  p + (m * p + n * p)
  ≡⟨ +-assoc-inv p (m * p) (n * p) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + m * n * p
  ≡⟨ cong (_+_ (n * p)) (*-assoc m n p) ⟩
   n * p + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎

-- (m + 1) * n
-- n + m * n
-- n * suc m

-- n + m * n
-- n + n * m
-- n + m * n
-- m - m + n + m * n
-- m + m * n


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m

*-proofSum : ∀ (n m : ℕ) → n + m * suc n ≡ m + n * suc m
*-proofSum n m = 
  begin
    n + m * suc n
  ≡⟨ cong (_+_ n) (*-comm m (suc n)) ⟩
    n + (m + n * m)
  ≡⟨ +-swap n m (n * m) ⟩
    m + (n + n * m)
    ≡⟨ cong (_+_ m) (
       begin
         n + n * m
       ≡⟨ cong (_+_ n) (*-comm n m) ⟩
         suc m * n
       ≡⟨ *-comm (suc m) n ⟩
         n * suc m
       ∎
    ) ⟩
    m + n * suc m
  ∎

*-comm zero zero = refl
*-comm zero (suc n) = *-comm zero n
*-comm (suc m) zero = *-comm m zero
*-comm (suc m) (suc n) =
  begin
    suc (n + m * suc n)
  ≡⟨ cong suc (*-proofSum n m) ⟩
    suc (m + n * suc m)
  ∎
