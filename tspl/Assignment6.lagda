# Name
Guilherme Horta Alvares da Silva

# Email
guilhermehas@hotmail.com

# Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Data.String.Unsafe using (_≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
\end{code}

# Exercise 1

\begin{code}
data Tree (A : Set) : Set where
  leaf : A → Tree A
  _branch_ : Tree A → Tree A → Tree A

data AllT (A : Set) (P : A → Set) : Tree A → Set where
  leaf : {x : A} → P x → AllT A P (leaf x)
  _branch_ : {xt yt : Tree A} → AllT A P xt → AllT A P yt → AllT A P (xt branch yt)

data AnyT (A : Set) (P : A → Set) : Tree A → Set where
  leaf : {x : A} → P x → AnyT A P (leaf x)
  left : {xt yt : Tree A} → AnyT A P xt → AnyT A P (xt branch yt)
  right : {xt yt : Tree A} → AnyT A P yt → AnyT A P (xt branch yt)

All¬T→¬AnyT : ∀ {A : Set} {P : A → Set} → {xt : Tree A} → AllT A (¬_ ∘ P) xt → ¬ (AnyT A P xt)
All¬T→¬AnyT (leaf ¬Px) (leaf Px) = ¬Px Px
All¬T→¬AnyT (allLeft branch _) (left anyLeft) = All¬T→¬AnyT allLeft anyLeft
All¬T→¬AnyT (_ branch allRight) (right anyRight) =  All¬T→¬AnyT allRight anyRight
\end{code}

# Exercise 3

\begin{code}
infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infix   6  _↑
infix   6  _↓_

Id : Set
Id = String

data Type : Set where
  `⊤    : Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A}
    --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    -----------------
    → Γ , y ⦂ B ∋ x ⦂ A

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  _↓_                      : Term⁻ → Type → Term⁺

data Term⁻ where
  `caseT_[tt⇒_]            : Term⁺ → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻
  `tt                      : Term⁻

data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where
  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
    ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where
  ⊢tt : ∀ {Γ}
    --------------
    → Γ ⊢ `tt ↓ `⊤

  ⊢caseT : ∀ {Γ L M A}
    → Γ ⊢ L ↑ `⊤
    → Γ ⊢ M ↓ A
    -------------
    → Γ ⊢ `caseT L [tt⇒ M ] ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
    -------------
    → Γ ⊢ (M ↑) ↓ B

_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`⊤ ≟Tp `⊤ = yes refl

uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z = refl
uniq-∋ Z (S x≠y _) = ⊥-elim (x≠y refl)
uniq-∋ (S x≢y _) Z = ⊥-elim (x≢y refl)
uniq-∋ (S _ ∋x) (S _ ∋x´) = uniq-∋ ∋x ∋x´

uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢↓ x) (⊢↓ x₁) = refl

ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ ∃[ A ]( Γ ∋ x ⦂ A )
  -----------------------------
  → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A )
ext∋ x≠y ¬∃ ⟨ fst , Z ⟩ = x≠y refl
ext∋ x≠y ¬∃ ⟨ A , S _ ⊢x ⟩ = ¬∃ ⟨ A , ⊢x ⟩

lookup : ∀ (Γ : Context) (x : Id)
  -----------------------
  → Dec (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x                        =  no  (λ ())
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                    =  yes ⟨ B , Z ⟩
... | no x≢y with lookup Γ x
...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
...             | yes ⟨ A , ⊢x ⟩  =  yes ⟨ A , S x≢y ⊢x ⟩

synthesize : ∀ (Γ : Context) (M : Term⁺)
  -----------------------
  → Dec (∃[ A ](Γ ⊢ M ↑ A))

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
  ---------------
  → Dec (Γ ⊢ M ↓ A)

synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩

inherit Γ `caseT L [tt⇒ M ] A with synthesize Γ L
... | no ¬∃ = no (λ{ (⊢caseT ⊢L _) → ¬∃ ⟨ `⊤ , ⊢L ⟩ })
... | yes ⟨ `⊤ , ⊢L ⟩ with inherit Γ M A
...    | no ¬∃ = no λ{ (⊢caseT ⊢L ⊢M) → ¬∃ ⊢M }
...    | yes ⊢M = yes (⊢caseT ⊢L ⊢M)
inherit Γ (M ↑) `⊤ with synthesize Γ M
...    | no ¬∃ = no λ{ (⊢↑ {_} {_} {`⊤} ⊢M _) → ¬∃ ⟨ `⊤ , ⊢M ⟩ }
...    | yes ⟨ `⊤ , ⊢M ⟩ = yes (⊢↑ ⊢M refl)
inherit Γ `tt `⊤ = yes ⊢tt

\end{code}
