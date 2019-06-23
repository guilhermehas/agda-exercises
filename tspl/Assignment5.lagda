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
    `⟨_,_⟩                   : Term⁻ → Term⁻ → Term⁻
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
      → Γ ⊢ M ↓ B
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
    -- end
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
  ... | yes ⊢A with inherit Γ M B
  ...   | no ¬∃   = no  λ{ (⊢⟨,⟩ ⊢A ⊢B) → ¬∃ ⊢B }
  ...   | yes ⊢B  = yes (⊢⟨,⟩ ⊢A ⊢B)
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

  dbtwo : ∀ {Γ} → Γ DB.⊢ DB.`ℕ
  dbtwo = DB.`suc DB.`suc DB.`zero

  dbplus : ∀ {Γ} → Γ DB.⊢ DB.`ℕ DB.⇒ DB.`ℕ DB.⇒ DB.`ℕ
  dbplus = DB.μ DB.ƛ DB.ƛ (DB.case (DB.# 1) (DB.# 0) (DB.`suc (DB.# 3 DB.· DB.# 0 DB.· DB.# 1)))

  dbmul : ∀ {Γ} → Γ DB.⊢ DB.`ℕ DB.⇒ DB.`ℕ DB.⇒ DB.`ℕ
  dbmul = DB.μ DB.ƛ DB.ƛ (DB.case (DB.# 0) DB.`zero (dbplus DB.· (DB.# 1) DB.· (DB.# 3 DB.· DB.# 0 DB.· DB.# 1)))

  db2*2 : ∀ {Γ} → Γ DB.⊢ DB.`ℕ
  db2*2 = dbmul DB.· dbtwo DB.· dbtwo

  dbCh : DB.Type → DB.Type
  dbCh A =  (A DB.⇒ A) DB.⇒ A DB.⇒ A

  dbtwoᶜ : ∀ {Γ A} → Γ DB.⊢ dbCh A
  dbtwoᶜ = DB.ƛ DB.ƛ (DB.# 1 DB.· (DB.# 1 DB.· DB.# 0))

  dbsucᶜ : ∀ {Γ} → Γ DB.⊢ DB.`ℕ DB.⇒ DB.`ℕ
  dbsucᶜ = DB.ƛ DB.`suc (DB.# 0)

  dbmulᶜ : ∀ {Γ A} → Γ DB.⊢ (dbCh A DB.⇒ (dbCh A DB.⇒ dbCh A))
  dbmulᶜ = DB.ƛ DB.ƛ DB.ƛ DB.ƛ (DB.# 3 DB.· (DB.# 2 DB.· DB.# 1) DB.· DB.# 0)

  db2*2ᶜ : ∀ {Γ} → Γ DB.⊢ DB.`ℕ
  db2*2ᶜ = dbmulᶜ DB.· dbtwoᶜ DB.· dbtwoᶜ DB.· dbsucᶜ DB.· DB.`zero

  2*2ᶜ : Term⁺
  2*2ᶜ = mulᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

  _ : synthesize ∅ 2*2 ≡ yes ⟨ `ℕ , ⊢2*2 ⟩
  _ = refl

  -- _ : ∥ ⊢2*2 ∥⁺ ≡ db2*2
  -- _ = refl

  -- _ : ∥ ⊢2*2ᶜ ∥⁺ ≡ db2*2ᶜ
  -- _ = refl
\end{code}

#### Exercise `inference-products` (recommended)

Extend bidirectional inference to include products from
Chapter [More][plfa.More].


#### Exercise `inference-rest` (stretch)

Extend bidirectional inference to include the rest of the constructs from
Chapter [More][plfa.More].

## Untyped

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

#### Exercise `encode-more` (stretch)

Along the lines above, encode all of the constructs of
Chapter [More][plfa.More],
save for primitive numbers, in the untyped lambda calculus.