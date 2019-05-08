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


⊎-elim : ∀ {A B C : Set} → (A ⊎ B) → (A → C) → (B → C) → C
⊎-elim (inj₁ a) ac _ = ac a
⊎-elim (inj₂ b) _ bc = bc b

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∃-intro : ∀ {A : Set} {B : A → Set} {C : A → Set}
  → ∃[ x ] B x
  → (∀ x → B x → C x)
  ---------------
  → ∃[ x ] C x
∃-intro ∃bx f = ∃-elim (λ x z → ⟨ x , f x z ⟩) ∃bx

postulate
  ∃-≡ : ∀ {A : Set} {B : A → Set}
    → (f : ∃[ x ] B x)
    → (g : ∃[ x ] B x)
    → f ≡ g

  ⊎-≡ : ∀ {B C : Set}
    → (f : B ⊎ C)
    → (g : B ⊎ C)
    → f ≡ g

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record {
  to = λ y → ∃-elim (λ a B⊎C → ⊎-elim B⊎C (λ Ba → inj₁ ⟨ a , Ba ⟩) λ z → inj₂ ⟨ a , z ⟩) y ;
  from = λ B⊎C → ⊎-elim B⊎C (λ ∃B → ∃-elim (λ x x₁ → ⟨ x , inj₁ x₁ ⟩) ∃B) λ ∃C → ∃-elim (λ x z → ⟨ x , inj₂ z ⟩) ∃C  ; 
  from∘to = λ x → ∃-≡ (⊎-elim
                         (∃-elim
                          (λ x₁ z →
                             ⊎-elim z (λ z₁ → inj₁ ⟨ x₁ , z₁ ⟩) (λ z₁ → inj₂ ⟨ x₁ , z₁ ⟩))
                          x)
                         (∃-elim (λ x₁ z → ⟨ x₁ , inj₁ z ⟩))
                         (∃-elim (λ x₁ z → ⟨ x₁ , inj₂ z ⟩))) x ;
  to∘from = λ y → ⊎-≡ (∃-elim
                         (λ x z →
                            ⊎-elim z (λ z₁ → inj₁ ⟨ x , z₁ ⟩) (λ z₁ → inj₂ ⟨ x , z₁ ⟩))
                         (⊎-elim y (∃-elim (λ x z → ⟨ x , inj₁ z ⟩))
                          (∃-elim (λ x z → ⟨ x , inj₂ z ⟩)))) y
  }


data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

can-isomorph :
    {Can : Bin → Set}
  → {from : Bin → ℕ}
  → {to : ℕ → Bin}
  → {eq : {n : ℕ} → from (to n) ≡ n}
  → {from∘to : {n : ℕ} → Can (to n)}
  → {to∘from : {b : Bin} → Can b → to (from b) ≡ b}
  → (∃[ x ] Can x) ≃ ℕ
can-isomorph {can} {from} {to} {eq} {from∘to} {to∘from} =
  record {
  to = λ f → ∃-elim (λ x _ → from x) f ;
  from = λ n → ⟨ (to n) , from∘to ⟩ ;
  from∘to = λ f → ∃-≡ ⟨ to (∃-elim (λ x _ → from x) f) , from∘to ⟩ f ;
  to∘from = λ y → eq
  }
