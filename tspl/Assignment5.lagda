---
title     : "PUC-Assignment5: PUC Assignment 5"
layout    : page
permalink : /PUC-Assignment5/
---

\begin{code}
module Assignment5 where
\end{code}

## YOUR NAME AND EMAIL GOES HERE

# Name
Guilherme Horta Alvares da Silva

# Email
guilhermehas@hotmail.com

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

**IMPORTANT** For ease of marking, when modifying the given code please write

    -- begin
    -- end

before and after code you add, to indicate your changes.


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String)
open import Data.String.Unsafe using (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
\end{code}

\begin{code}
module db where
  open import plfa.More
  two : ∀ {Γ} → Γ ⊢ `ℕ
  two = `suc `suc `zero

  plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
  plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

  mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
  mul = μ ƛ ƛ (case (# 0) `zero (plus · (# 1) · (# 3 · # 0 · # 1)))

  2*2 : ∀ {Γ} → Γ ⊢ `ℕ
  2*2 = mul · two · two

  Ch : Type → Type
  Ch A =  (A ⇒ A) ⇒ A ⇒ A

  twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
  twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

  sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
  sucᶜ = ƛ `suc (# 0)

  mulᶜ : ∀ {Γ A} → Γ ⊢ (Ch A ⇒ (Ch A ⇒ Ch A))
  mulᶜ = ƛ ƛ ƛ ƛ (# 3 · (# 2 · # 1) · # 0)

  2*2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
  2*2ᶜ = mulᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
\end{code}

## Inference

\begin{code}
module Inference where
\end{code}

Remember to indent all code by two spaces.

### Imports

\begin{code}
  import plfa.More as DB
\end{code}

### Syntax

\begin{code}
  infix   4  _∋_⦂_
  infix   4  _⊢_↑_
  infix   4  _⊢_↓_
  infixl  5  _,_⦂_

  infixr  7  _⇒_

  infix   5  ƛ_⇒_
  infix   5  μ_⇒_
  infix   6  _↑
  infix   6  _↓_
  infixl  7  _·_
  infix   8  `suc_
  infix   9  `_
\end{code}

### Identifiers, types, and contexts

\begin{code}
  Id : Set
  Id = String

  data Type : Set where
    `ℕ    : Type
    _⇒_   : Type → Type → Type
    -- begin
    _`×_  : Type → Type → Type
    -- end

  data Context : Set where
    ∅     : Context
    _,_⦂_ : Context → Id → Type → Context
\end{code}

### Terms

\begin{code}
  data Term⁺ : Set
  data Term⁻ : Set

  data Term⁺ where
    `_                        : Id → Term⁺
    _·_                       : Term⁺ → Term⁻ → Term⁺
    _↓_                       : Term⁻ → Type → Term⁺

  data Term⁻ where
    ƛ_⇒_                     : Id → Term⁻ → Term⁻
    `zero                    : Term⁻
    `suc_                    : Term⁻ → Term⁻
    `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  -- begin

  -- Product
    `⟨_,_⟩                   : Term⁻ → Term⁻ → Term⁻
    `proj₁_                   : Term⁻ → Term⁻
    `proj₂_                   : Term⁻ → Term⁻
  -- end
    μ_⇒_                     : Id → Term⁻ → Term⁻
    _↑                       : Term⁺ → Term⁻
\end{code}

### Sample terms

\begin{code}
  two : Term⁻
  two = `suc (`suc `zero)

  plus : Term⁺
  plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
            `case (` "m") [zero⇒ ` "n" ↑
                          |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
              ↓ `ℕ ⇒ `ℕ ⇒ `ℕ

  2+2 : Term⁺
  2+2 = plus · two · two
\end{code}

### Lookup

\begin{code}
  data _∋_⦂_ : Context → Id → Type → Set where

    Z : ∀ {Γ x A}
        --------------------
      → Γ , x ⦂ A ∋ x ⦂ A

    S : ∀ {Γ x y A B}
      → x ≢ y
      → Γ ∋ x ⦂ A
        -----------------
      → Γ , y ⦂ B ∋ x ⦂ A
\end{code}

### Bidirectional type checking

\begin{code}
  data _⊢_↑_ : Context → Term⁺ → Type → Set
  data _⊢_↓_ : Context → Term⁻ → Type → Set

  data _⊢_↑_ where

    ⊢` : ∀ {Γ A x}
      → Γ ∋ x ⦂ A
        -----------
      → Γ ⊢ ` x ↑ A

    _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ↑ A ⇒ B
      → Γ ⊢ M ↓ A
        -------------
      → Γ ⊢ L · M ↑ B

    ⊢↓ : ∀ {Γ M A}
      → Γ ⊢ M ↓ A
        ---------------
      → Γ ⊢ (M ↓ A) ↑ A

  data _⊢_↓_ where

    ⊢ƛ : ∀ {Γ x N A B}
      → Γ , x ⦂ A ⊢ N ↓ B
        -------------------
      → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

    ⊢zero : ∀ {Γ}
        --------------
      → Γ ⊢ `zero ↓ `ℕ

    ⊢suc : ∀ {Γ M}
      → Γ ⊢ M ↓ `ℕ
        ---------------
      → Γ ⊢ `suc M ↓ `ℕ

    ⊢case : ∀ {Γ L M x N A}
      → Γ ⊢ L ↑ `ℕ
      → Γ ⊢ M ↓ A
      → Γ , x ⦂ `ℕ ⊢ N ↓ A
        -------------------------------------
      → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

    -- begin
    ⊢⟨,⟩ : ∀ {Γ A B M N}
      → Γ ⊢ M ↓ A
      → Γ ⊢ N ↓ B
      ----------------
      → Γ ⊢ `⟨ M , N ⟩ ↓ A `× B
    -- end

    ⊢μ : ∀ {Γ x N A}
      → Γ , x ⦂ A ⊢ N ↓ A
        -----------------
      → Γ ⊢ μ x ⇒ N ↓ A

    ⊢↑ : ∀ {Γ M A B}
      → Γ ⊢ M ↑ A
      → A ≡ B
        -------------
      → Γ ⊢ (M ↑) ↓ B
\end{code}


### Type equality

\begin{code}
  _≟Tp_ : (A B : Type) → Dec (A ≡ B)
  `ℕ      ≟Tp `ℕ              =  yes refl
  `ℕ      ≟Tp (A ⇒ B)         =  no λ()
  (A ⇒ B) ≟Tp `ℕ              =  no λ()
  (A ⇒ B) ≟Tp (A′ ⇒ B′)
    with A ≟Tp A′ | B ≟Tp B′
  ...  | no A≢    | _         =  no λ{refl → A≢ refl}
  ...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
  ...  | yes refl | yes refl  =  yes refl
  -- begin
  (A `× B) ≟Tp `ℕ = no λ()
  `ℕ ≟Tp (A `× B) = no λ()
  (A ⇒ B) ≟Tp (C `× D) = no λ()
  (A `× B) ≟Tp (C ⇒ D) = no λ()
  (A `× B) ≟Tp (C `× D)
    with A ≟Tp C  | B ≟Tp D
  ...  | no A≠    | _        = no λ{refl → A≠ refl}
  ...  | yes _    | no B≠    = no λ{refl → B≠ refl}
  ...  | yes refl | yes refl = yes refl
  -- end
\end{code}

### Prerequisites

\begin{code}
  dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
  dom≡ refl = refl

  rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
  rng≡ refl = refl

  ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
  ℕ≢⇒ ()

  -- begin
  ×≢⇒ : ∀ {A B C D} → A `× B ≢ C ⇒ D
  ×≢⇒ ()

  ×≢ℕ : ∀ {A B} → A `× B ≢ `ℕ
  ×≢ℕ ()
  -- end
\end{code}


### Unique lookup

\begin{code}
  uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  uniq-∋ Z Z                 =  refl
  uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
  uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
  uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
\end{code}

### Unique synthesis

\begin{code}
  uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
  uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
  uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
  uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl
\end{code}

## Lookup type of a variable in the context

\begin{code}
  ext∋ : ∀ {Γ B x y}
    → x ≢ y
    → ¬ ∃[ A ]( Γ ∋ x ⦂ A )
      -----------------------------
    → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A )
  ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
  ext∋ _   ¬∃ ⟨ A , S _ ⊢x ⟩  =  ¬∃ ⟨ A , ⊢x ⟩

  lookup : ∀ (Γ : Context) (x : Id)
      -----------------------
    → Dec (∃[ A ](Γ ∋ x ⦂ A))
  lookup ∅ x                        =  no  (λ ())
  lookup (Γ , y ⦂ B) x with x ≟ y
  ... | yes refl                    =  yes ⟨ B , Z ⟩
  ... | no x≢y with lookup Γ x
  ...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
  ...             | yes ⟨ A , ⊢x ⟩  =  yes ⟨ A , S x≢y ⊢x ⟩
\end{code}

### Promoting negations

\begin{code}
  ¬arg : ∀ {Γ A B L M}
    → Γ ⊢ L ↑ A ⇒ B
    → ¬ Γ ⊢ M ↓ A
      -------------------------
    → ¬ ∃[ B′ ](Γ ⊢ L · M ↑ B′)
  ¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

  ¬switch : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≢ B
      ---------------
    → ¬ Γ ⊢ (M ↑) ↓ B
  ¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B
\end{code}


## Synthesize and inherit types

\begin{code}
  synthesize : ∀ (Γ : Context) (M : Term⁺)
      -----------------------
    → Dec (∃[ A ](Γ ⊢ M ↑ A))

  inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
      ---------------
    → Dec (Γ ⊢ M ↓ A)

  synthesize Γ (` x) with lookup Γ x
  ... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
  ... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
  synthesize Γ (L · M) with synthesize Γ L
  ... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
  ... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
  -- begin
  ... | yes ⟨ A `× B , ⊢L ⟩ = no λ { ⟨ _ , ⊢L´ · _ ⟩ → ×≢⇒ (uniq-↑ ⊢L ⊢L´)}
  -- end
  ... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
  ...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
  ...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩
  synthesize Γ (M ↓ A) with inherit Γ M A
  ... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
  ... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩

  inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
  inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
  ... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
  ... | yes ⊢N                =  yes (⊢ƛ ⊢N)
  inherit Γ `zero `ℕ          =  yes ⊢zero
  inherit Γ `zero (A ⇒ B)     =  no  (λ())
  inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
  ... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
  ... | yes ⊢M                =  yes (⊢suc ⊢M)
  inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
  inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
  ... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
  ... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })
  -- begin
  ... | yes ⟨ P `× Q , ⊢LPQ ⟩ = no (λ{ (⊢case ⊢L′ _ _) → ×≢ℕ (uniq-↑ ⊢LPQ ⊢L′) })
  -- end
  ... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
  ...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
  ...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
  ...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
  ...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
  inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
  ... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
  ... | yes ⊢N                =  yes (⊢μ ⊢N)
  inherit Γ (M ↑) B with synthesize Γ M
  ... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
  ... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
  ...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
  ...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)
  -- begin
  inherit Γ `⟨ M , N ⟩ `ℕ       = no λ()
  inherit Γ `⟨ M , N ⟩ (A ⇒ B)  = no λ()
  inherit Γ (ƛ x ⇒ M) (A `× B)  = no λ()
  inherit Γ `zero (A `× B)      = no λ()
  inherit Γ (`suc M) (A `× B)   = no λ()
  inherit Γ `⟨ M , N ⟩ (A `× B) with inherit Γ M A
  ... | no ¬∃ = no (λ{ (⊢⟨,⟩ ⊢A ⊢B) → ¬∃ ⊢A })
  ... | yes ⊢A with inherit Γ N B
  ...   | no ¬∃   = no  λ{ (⊢⟨,⟩ ⊢A ⊢B) → ¬∃ ⊢B }
  ...   | yes ⊢B  = yes (⊢⟨,⟩ ⊢A ⊢B)
  inherit Γ (`proj₁ _) `ℕ       = no λ()
  inherit Γ (`proj₂ _) `ℕ       = no λ()
  inherit Γ (`proj₁ _) (_ ⇒ _)   = no λ()
  inherit Γ (`proj₂ _) (_ ⇒ _)   = no λ()
  inherit Γ (`proj₁ _) (_ `× _)  = no λ()
  inherit Γ (`proj₂ _) (_ `× _)  = no λ()
  -- end
\end{code}

### Erasure

\begin{code}
  ∥_∥Tp : Type → DB.Type
  ∥ `ℕ ∥Tp             =  DB.`ℕ
  ∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp
  -- begin
  ∥ A `× B ∥Tp         = ∥ A ∥Tp DB.`× ∥ B ∥Tp
  -- end

  ∥_∥Cx : Context → DB.Context
  ∥ ∅ ∥Cx              =  DB.∅
  ∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp

  ∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
  ∥ Z ∥∋               =  DB.Z
  ∥ S x≢ ⊢x ∥∋         =  DB.S ∥ ⊢x ∥∋

  ∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
  ∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

  ∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
  ∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
  ∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

  ∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
  ∥ ⊢zero ∥⁻           =  DB.`zero
  ∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
  ∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
  ∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
  ∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺
  -- begin
  ∥ (⊢⟨,⟩ ⊢A ⊢B) ∥⁻    = DB.`⟨ ∥ ⊢A ∥⁻ , ∥ ⊢B ∥⁻ ⟩
  -- end
\end{code}


#### Exercise `bidirectional-mul` (recommended) {#bidirectional-mul}

Rewrite your definition of multiplication from
Chapter [Lambda][plfa.Lambda], decorated to support inference.

\begin{code}
  mul : Term⁺
  mul = (μ "mul" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
    `case (` "m") [zero⇒ `zero
                  |suc "m" ⇒ plus · (` "m" ↑) · (` "mul" · (` "m" ↑) · (` "n" ↑) ↑) ↑ ])
    ↓ `ℕ ⇒ `ℕ ⇒ `ℕ
\end{code}

#### Exercise `bidirectional-products` (recommended) {#bidirectional-products}

Extend the bidirectional type rules to include products from
Chapter [More][plfa.More].


#### Exercise `bidirectional-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More][plfa.More].


#### Exercise `inference-mul` (recommended)

Using the definition from exercise [bidirectional-mul](#bidirectional-mul),
infer the corresponding inherently typed term.
Show that erasure of the inferred typing yields your definition of
multiplication from Chapter [DeBruijn][plfa.DeBruijn].

\begin{code}
  _≠_ : ∀ (x y : Id) → x ≢ y
  x ≠ y  with x ≟ y
  ...       | no  x≢y  =  x≢y
  ...       | yes _    =  ⊥-elim impossible
    where postulate impossible : ⊥

  Ch : Type
  Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

  sucᶜ : Term⁻
  sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

  twoᶜ : Term⁻
  twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

  mulᶜ : Term⁺
  mulᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
              ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
              ↓ (Ch ⇒ Ch ⇒ Ch)

  2*2 : Term⁺
  2*2 = mul · two · two

  ⊢2*2 : ∅ ⊢ 2*2 ↑ `ℕ
  ⊢2*2 = ⊢↓
           (⊢μ
            (⊢ƛ
             (⊢ƛ
              (⊢case (⊢` (S ("m" ≠ "n") Z)) ⊢zero
               (⊢↑
                (⊢↓
                 (⊢μ
                  (⊢ƛ
                   (⊢ƛ
                    (⊢case (⊢` (S ("m" ≠ "n") Z))
                     (⊢↑ (⊢` Z) refl)
                     (⊢suc
                      (⊢↑
                       (⊢`
                        (S ("p" ≠ "m")
                        (S ("p" ≠ "n")
                        (S ("p" ≠ "m") Z)))
                        · ⊢↑ (⊢` Z) refl
                        · ⊢↑ (⊢` (S ("n" ≠ "m") Z)) refl)
                       refl))))))
                 · ⊢↑ (⊢` Z) refl
                 ·
                 ⊢↑
                 (⊢`
                 (S ("mul" ≠ "m")
                 (S ("mul" ≠ "n")
                 (S ("mul" ≠ "m") Z)))
                  · ⊢↑ (⊢` Z) refl
                  · ⊢↑ (⊢` (S ("n" ≠ "m") Z)) refl)
                 refl)
                refl)))))
           · ⊢suc (⊢suc ⊢zero) · (⊢suc (⊢suc ⊢zero))


  2*2ᶜ : Term⁺
  2*2ᶜ = mulᶜ · twoᶜ · twoᶜ · sucᶜ · `zero


  ⊢mul : ∅ ⊢ mul ↑ `ℕ ⇒ `ℕ ⇒ `ℕ
  ⊢mul = ⊢↓ (⊢μ
              (⊢ƛ
               (⊢ƛ
                (⊢case (⊢` (S ("m" ≠ "n") Z)) ⊢zero
                 (⊢↑
                  (⊢↓
                   (⊢μ
                    (⊢ƛ
                     (⊢ƛ
                      (⊢case (⊢` (S ("m" ≠ "n") Z))
                       (⊢↑ (⊢` Z) refl)
                       (⊢suc
                        (⊢↑
                         (⊢`
                          (S ("p" ≠ "m")
                           (S ("p" ≠ "n")
                            (S ("p" ≠ "m") Z)))
                          · ⊢↑ (⊢` Z) refl
                          · ⊢↑ (⊢` (S ("n" ≠ "m") Z)) refl)
                         refl))))))
                   · ⊢↑ (⊢` Z) refl
                   ·
                   ⊢↑
                   (⊢`
                    (S ("mul" ≠ "m")
                     (S ("mul" ≠ "n")
                      (S ("mul" ≠ "m") Z)))
                    · ⊢↑ (⊢` Z) refl
                    · ⊢↑ (⊢` (S ("n" ≠ "m") Z)) refl)
                   refl)
                  refl)))))

  _ : synthesize ∅ mul ≡ yes ⟨ `ℕ ⇒ `ℕ ⇒ `ℕ , ⊢mul ⟩
  _ = refl

  _ : synthesize ∅ 2*2 ≡ yes ⟨ `ℕ , ⊢2*2 ⟩
  _ = refl
\end{code}

#### Exercise `inference-products` (recommended)

Extend bidirectional inference to include products from
Chapter [More][plfa.More].


#### Exercise `inference-rest` (stretch)

Extend bidirectional inference to include the rest of the constructs from
Chapter [More][plfa.More].

## Untyped

\begin{code}
module Untyped where
  open import plfa.Untyped
\end{code}

#### Exercise (`Type≃⊤`)

Show that `Type` is isomorphic to `⊤`, the unit type.

#### Exercise (`Context≃ℕ`)

Show that `Context` is isomorphic to `ℕ`.

#### Exercise (`variant-1`)

How would the rules change if we want call-by-value where terms
normalise completely?  Assume that `β` should not permit reduction
unless both terms are in normal form.

#### Exercise (`variant-2`)

How would the rules change if we want call-by-value where terms
do not reduce underneath lambda?  Assume that `β`
permits reduction when both terms are values (that is, lambda
abstractions).  What would `2+2ᶜ` reduce to in this case?

#### Exercise `plus-eval`

Use the evaluator to confirm that `plus · two · two` and `four`
normalise to the same term.

#### Exercise `multiplication-untyped` (recommended)

Use the encodings above to translate your definition of
multiplication from previous chapters with the Scott
representation and the encoding of the fixpoint operator.
Confirm that two times two is four.

\begin{code}
  mul : ∀ {Γ} → Γ ⊢ ★
  mul = μ ƛ ƛ (case (# 0) `zero (plus · # 1 · (# 3 · # 0 · # 1)))

  mulᶜ : ∀ {Γ} → Γ ⊢ ★
  mulᶜ = ƛ ƛ ƛ ƛ (# 3 · (# 2 · # 1) · # 0)

  2*2ᶜ : ∅ ⊢ ★
  2*2ᶜ = mulᶜ · twoᶜ · twoᶜ

  _ : eval (gas 100) 2*2ᶜ ≡
    steps
      ((ƛ
        (ƛ
        (ƛ (ƛ (` (S (S (S Z)))) · ((` (S (S Z))) · (` (S Z))) · (` Z)))))
      · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
      · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
      —→⟨ ξ₁ ap β ⟩
      (ƛ
        (ƛ
        (ƛ
          (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) ·
          ((` (S (S Z))) · (` (S Z)))
          · (` Z))))
      · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
      —→⟨ β ⟩
      ƛ
      (ƛ
        (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)))
        · (` Z))
      —→⟨ ζ (ζ (ξ₁ ap β)) ⟩
      ƛ
      (ƛ
        (ƛ
        (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S (S Z))) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S (S Z))) · (` Z)))
        · (` Z))
      —→⟨ ζ (ζ β) ⟩
      ƛ
      (ƛ
        (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
      —→⟨ ζ (ζ (ξ₁ ap β)) ⟩
      ƛ
      (ƛ
        (ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
      —→⟨ ζ (ζ β) ⟩
      ƛ
      (ƛ
        (` (S Z)) ·
        ((` (S Z)) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z))))
      —→⟨ ζ (ζ (ξ₂ (` (S Z)) (ξ₂ (` (S Z)) (ξ₁ ap β)))) ⟩
      ƛ
      (ƛ
        (` (S Z)) ·
        ((` (S Z)) ·
        ((ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) · (` Z))))
      —→⟨ ζ (ζ (ξ₂ (` (S Z)) (ξ₂ (` (S Z)) β))) ⟩
      ƛ (ƛ (` (S Z)) · ((` (S Z)) · ((` (S Z)) · ((` (S Z)) · (` Z)))))
      ∎)
      (done
      (ƛ
        (ƛ
        (′
          (` (S Z)) ·
          (′ (` (S Z)) · (′ (` (S Z)) · (′ (` (S Z)) · (′ (` Z)))))))))
  _ = refl
\end{code}

#### Exercise `encode-more` (stretch)

Along the lines above, encode all of the constructs of
Chapter [More][plfa.More],
save for primitive numbers, in the untyped lambda calculus.

\begin{code}
module ExtendedUntyped where
  infix  4  _⊢_
  infix  4  _∋_
  infixl 5  _,_

  infix  6  ƛ_
  -- infix  6  ′_
  infixl 7  _·_

  data Type : Set where
    ★ : Type

  data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context

  data _∋_ : Context → Type → Set where

    Z : ∀ {Γ A}
      ---------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
      ---------
      → Γ , B ∋ A

  data _⊢_ : Context → Type → Set where

    `_ : ∀ {Γ A}
      → Γ ∋ A
      -----
      → Γ ⊢ A

    ƛ_  :  ∀ {Γ}
      → Γ , ★ ⊢ ★
      ---------
      → Γ ⊢ ★

    _·_ : ∀ {Γ}
      → Γ ⊢ ★
      → Γ ⊢ ★
      ------
      → Γ ⊢ ★

  -- begin

  -- Product
    `⟨_,_⟩ : ∀ {Γ}
      → Γ ⊢ ★
      → Γ ⊢ ★
      -----------
      → Γ ⊢ ★

    `proj₁ : ∀ {Γ}
      → Γ ⊢ ★
      -----------
      → Γ ⊢ ★

    `proj₂ : ∀ {Γ}
      → Γ ⊢ ★
      -----------
      → Γ ⊢ ★

  -- List
    `[] : ∀ {Γ}
    -----------
      → Γ ⊢ ★

    _`∷_ : ∀ {Γ}
      → Γ ⊢ ★
      → Γ ⊢ ★
    -----------
      → Γ ⊢ ★

    `head_ : ∀ {Γ}
      → Γ ⊢ ★
      -----------
      → Γ ⊢ ★

    `tail_ : ∀ {Γ}
      → Γ ⊢ ★
      -----------
      → Γ ⊢ ★

  -- end


  count : ∀ {Γ} → ℕ → Γ ∋ ★
  count {Γ , ★} zero     =  Z
  count {Γ , ★} (suc n)  =  S (count n)
  count {∅}     _        =  ⊥-elim impossible
    where postulate impossible : ⊥

  #_ : ∀ {Γ} → ℕ → Γ ⊢ ★
  # n  =  ` count n

  twoᶜ : ∀ {Γ} → Γ ⊢ ★
  twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

  fourᶜ : ∀ {Γ} → Γ ⊢ ★
  fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

  plusᶜ : ∀ {Γ} → Γ ⊢ ★
  plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

  2+2ᶜ : ∅ ⊢ ★
  2+2ᶜ = plusᶜ · twoᶜ · twoᶜ

  ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  rename ρ (` x)          =  ` (ρ x)
  rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
  rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
  -- begin
  rename ρ `⟨ L , M ⟩     =  `⟨ rename ρ L , rename ρ M ⟩
  rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
  rename ρ (`proj₂ M)     =  `proj₂ (rename ρ M)
  rename ρ (`[])          =  `[]
  rename ρ (x `∷ xs)      =  rename ρ x `∷  rename ρ xs
  rename ρ (`head xs)     =  `head (rename ρ xs)
  rename ρ (`tail xs)     =  `tail (rename ρ xs)
  -- end


  exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
  exts σ Z      =  ` Z
  exts σ (S x)  =  rename S_ (σ x)

  subst : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  subst σ (` k)          =  σ k
  subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
  subst σ (L · M)        =  (subst σ L) · (subst σ M)
  -- begin
  subst σ `⟨ L , M ⟩     =  `⟨ subst σ L , subst σ M ⟩
  subst σ (`proj₁ L)      =  `proj₁ (subst σ L)
  subst σ (`proj₂ M)      =  `proj₂ (subst σ M)
  subst σ (`[])           =  `[]
  subst σ (x `∷ xs)       =  subst σ x `∷ subst σ xs
  subst σ (`head xs)      =  `head (subst σ xs)
  subst σ (`tail xs)      =  `tail (subst σ xs)
  -- end

  subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
  subst-zero M Z      =  M
  subst-zero M (S x)  =  ` x

  _[_] : ∀ {Γ A B}
    → Γ , B ⊢ A
    → Γ ⊢ B
    ---------
    → Γ ⊢ A
  _[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N

  data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
  data Normal  : ∀ {Γ A} → Γ ⊢ A → Set

  data Neutral where

    `_  : ∀ {Γ A} (x : Γ ∋ A)
      -------------
      → Neutral (` x)

    _·_  : ∀ {Γ} {L M : Γ ⊢ ★}
      → Neutral L
      → Normal M
      ---------------
      → Neutral (L · M)

  -- begin
    `⟨_,_⟩  : ∀ {Γ} {L M : Γ ⊢ ★}
      → Neutral L
      → Neutral M
      ---------------
      → Neutral `⟨ L , M ⟩

    `[]  : ∀ {Γ}
      ---------------
      → Neutral {Γ} `[]

    _`∷_  : ∀ {Γ} {L M : Γ ⊢ ★}
      → Neutral L
      → Neutral M
      ---------------
      → Neutral (L `∷ M)
  -- end

  data Normal where

    ′_ : ∀ {Γ A} {M : Γ ⊢ A}
      → Neutral M
      ---------
      → Normal M

    ƛ_  : ∀ {Γ} {N : Γ , ★ ⊢ ★}
      → Normal N
      ------------
      → Normal (ƛ N)

  #′_ : ∀ {Γ} (n : ℕ) → Neutral {Γ} (# n)
  #′ n  =  ` count n



  data Application : ∀ {Γ A} → Γ ⊢ A → Set where

    ap : ∀ {Γ} {L M : Γ ⊢ ★}
      -------------------
      → Application (L · M)

  infix 2 _—→_

  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
      → Application L
      → L —→ L′
      ----------------
      → L · M —→ L′ · M

    ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
      → Neutral L
      → M —→ M′
      ----------------
      → L · M —→ L · M′

    β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
      ---------------------------------
      → (ƛ N) · M —→ N [ M ]

    ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
      → N —→ N′
      -----------
      → ƛ N —→ ƛ N′

  -- begin

    -- Products

    ξ-⟨,⟩₁ : ∀ {Γ} {M M′ N : Γ ⊢ ★}
      → M —→ M′
      -------------------------
      → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    ξ-⟨,⟩₂ : ∀ {Γ} {V N N′ : Γ ⊢ ★}
      → Neutral V
      → N —→ N′
      -------------------------
      → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    ξ-proj₁ : ∀ {Γ} {L L′ : Γ ⊢ ★}
      → L —→ L′
      ---------------------
      → `proj₁ L —→ `proj₁ L′

    ξ-proj₂ : ∀ {Γ} {L L′ : Γ ⊢ ★}
      → L —→ L′
      ---------------------
      → `proj₂ L —→ `proj₂ L′

    β-proj₁ : ∀ {Γ} {V W : Γ ⊢ ★}
      → Neutral V
      → Neutral W
      ----------------------
      → `proj₁ `⟨ V , W ⟩ —→ V

    β-proj₂ : ∀ {Γ} {V W : Γ ⊢ ★}
      → Neutral V
      → Neutral W
      ----------------------
      → `proj₂ `⟨ V , W ⟩ —→ W

    -- Lists

    ξ-cons₁ : ∀ {Γ} {x x´ xs : Γ ⊢ ★}
      → x —→ x´
      ----------------------
      → x `∷ xs —→ x´ `∷ xs

    ξ-cons₂ : ∀ {Γ} {x xs xs´ : Γ ⊢ ★}
      → Neutral x
      → xs —→ xs´
      ----------------------
      → x `∷ xs —→ x `∷ xs´

    β-head : ∀ {Γ} {x xs : Γ ⊢ ★}
      → Neutral x
      → Neutral xs
      ----------------------
      → `head (x `∷ xs) —→ x

    β-tail : ∀ {Γ} {x xs : Γ ⊢ ★}
      → Neutral x
      → Neutral xs
      ----------------------
      → `tail (x `∷ xs) —→ xs
  -- end

\end{code}
