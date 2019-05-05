---
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /Assignment2/
---

\begin{code}
module Assignment2 where
\end{code}

## Name
Guilherme Horta Alvares da Silva

## Email
guilhermehas@hotmail.com

## Introduction

<!-- This assignment is due **4pm Thursday 18 October** (Week 5). -->

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

<!-- Submit your homework using the "submit" command. -->
Please ensure your files execute correctly under Agda!

## Imports

\begin{code}
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
\end{code}

## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.

\begin{code}
module ≤-Reasoning where

  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  1 begin≤_

  begin≤_ : ∀ {x y : ℕ} → x ≡ y → x ≡ y
  begin≤_ eq = eq

  _≤⟨⟩_ : ∀ (x {y} : ℕ) → x ≤ y → x ≤ y
  _ ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x {y z} : ℕ) → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

\end{code}

## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
\begin{code}
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B  

≃-implies-≲ record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } = record { to = to ; from = from ; from∘to = from∘to }
\end{code}

#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
\begin{code}
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

if_onlyif_ : ∀ (A B : Set) → Set
if A onlyif B = A ⇔ B
\end{code}
Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
\begin{code}
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
\end{code}
And ask you to define the following functions:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
Why is there not an isomorphism?

```
  There are not two different naturals that is represented by same binary number. So from (to n) ≡ n.
  But two binary represent can represent the same number. For exemple from (x1 x0 nil) ≡ from (x1 nil) ≡ 1 . x1 nil ≡ to (from (x1 nil)) ≡ to (from (x1 x0 nil)) ≠ x1 x0 nil
```

## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.

\begin{code}
⇔≃×ˡ : ∀ {A B : Set} → (A ⇔ B) → ((A → B) × (B → A))
⇔≃×ˡ record { to = to ; from = from } = ⟨ to , from ⟩

⇔≃×ʳ : ∀ {A B : Set} → ((A → B) × (B → A)) → (A ⇔ B)
⇔≃×ʳ ⟨ fst , snd ⟩ = record { to = fst ; from = snd }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ⇔ ((A → B) × (B → A))
⇔≃× = record { to = ⇔≃×ˡ ; from =  ⇔≃×ʳ }
\end{code}

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

\begin{code}
⊎-commˡ : ∀ {A B : Set} → (A ⊎ B) → (B ⊎ A)
⊎-commˡ (inj₁ x) = inj₂ x
⊎-commˡ (inj₂ y) = inj₁ y

⊎-comm : ∀ {A B : Set} → (A ⊎ B) ⇔ (B ⊎ A)
⊎-comm = record { to = ⊎-commˡ ; from = ⊎-commˡ }
\end{code}

#### Exercise `⊎-assoc`

Show sum is associative up to ismorphism. 

\begin{code}
⊎-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ⇔ (A ⊎ (B ⊎ C))
⊎-assoc = record { to = ⊎-assocˡ ; from = ⊎-assocʳ }
  where
    ⊎-assocˡ : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
    ⊎-assocˡ (inj₁ (inj₁ a)) = inj₁ a
    ⊎-assocˡ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
    ⊎-assocˡ (inj₂ c) = inj₂ (inj₂ c)

    ⊎-assocʳ : ∀ {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
    ⊎-assocʳ (inj₁ a) = inj₁ (inj₁ a)
    ⊎-assocʳ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
    ⊎-assocʳ (inj₂ (inj₂ c)) = inj₂ c
\end{code}

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

\begin{code}
⊥-identityˡ : ∀ {A : Set} → (⊥ ⊎ A) ⇔ A
⊥-identityˡ = record { to =  ⊥-identityˡˡ ; from =  ⊥-identityˡʳ }
  where
    ⊥-identityˡˡ : ∀ {A : Set} → (⊥ ⊎ A) → A
    ⊥-identityˡˡ (inj₁ ())
    ⊥-identityˡˡ (inj₂ a) = a

    ⊥-identityˡʳ : ∀ {A : Set} → A → (⊥ ⊎ A)
    ⊥-identityˡʳ a = inj₂ a
\end{code}

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition. 


\begin{code}
⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ⇔ A
⊥-identityʳ = record { to =  ⊥-identityʳˡ ; from =  ⊥-identityʳʳ }
  where
    ⊥-identityʳˡ : ∀ {A : Set} → (A ⊎ ⊥) → A
    ⊥-identityʳˡ (inj₁ a) = a
    ⊥-identityʳˡ (inj₂ ())

    ⊥-identityʳʳ : ∀ {A : Set} → A → (A ⊎ ⊥)
    ⊥-identityʳʳ a = inj₁ a
\end{code}

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
\begin{code}
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , _ ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

\end{code}
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
Does the converse hold? If so, prove; if not, give a counterexample.

\begin{code}
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩
\end{code}

## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.

\begin{code}
<-irreflexive : ∀ n → ¬ (n < n)
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n
\end{code}

#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.

\begin{code}
data Ordering : ℕ → ℕ → Set where
  less : {m n : ℕ} → (m < n) → Ordering m n
  equal : {m n : ℕ} → (m ≡ n) → Ordering m n
  greater : {m n : ℕ} → (n < m) → Ordering m n

≡-same : ∀ {m n : ℕ} → m ≡ n → n ≡ m
≡-same refl = refl

<-≡-disjoint : ∀ {m n} → (m < n) → (m ≡ n) → ⊥
<-≡-disjoint (s<s m<n) refl = <-≡-disjoint m<n refl

<->-disjoint : ∀ {m n} → (m < n) → (n < m) → ⊥
<->-disjoint z<s ()
<->-disjoint (s<s m<n) (s<s n<m) = <->-disjoint m<n n<m

<-unique : ∀ {m n : ℕ} → (x : m < n) → (y : m < n) → x ≡ y
<-unique z<s z<s = refl
<-unique (s<s x) (s<s y) = cong s<s (<-unique x y)

≡-unique : ∀ {m n : ℕ} → (x : m ≡ n) → (y : m ≡ n) → x ≡ y
≡-unique refl refl = refl

trichotomy : ∀ {m n : ℕ} → (x : Ordering m n) → (y : Ordering m n) → x ≡ y
trichotomy (less x) (less y) = cong less (<-unique x y)
trichotomy (less x) (equal y) = ⊥-elim (<-≡-disjoint x y)
trichotomy (less x) (greater y) = ⊥-elim  (<->-disjoint x y)
trichotomy (equal x) (less y) = ⊥-elim  (<-≡-disjoint y x)
trichotomy (equal x) (equal y) = cong equal (≡-unique x y)
trichotomy (equal x) (greater y) = ⊥-elim  (<-≡-disjoint y (≡-same x))
trichotomy (greater x) (less y) = ⊥-elim  (<->-disjoint y x)
trichotomy (greater x) (equal y) = ⊥-elim (<-≡-disjoint x (≡-same y))
trichotomy (greater x) (greater y) = cong greater (<-unique x y)
\end{code}


#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, give a variant that does hold.
\begin{code}
⊎-dual-×-to : ∀ {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
⊎-dual-×-to ¬ab = ⟨ (λ a → ¬ab (inj₁ a)) , (λ b → ¬ab (inj₂ b)) ⟩

⊎-dual-×-from : ∀ {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
⊎-dual-×-from ⟨ ¬a , _ ⟩ (inj₁ a) = ¬a a
⊎-dual-×-from ⟨ _ , ¬b ⟩ (inj₂ b) = ¬b b

⊎-dual-×-from∘to : ∀ {A B : Set} (¬a⊎b : ¬ (A ⊎ B)) → ⊎-dual-×-from (⊎-dual-×-to ¬a⊎b) ≡ ¬a⊎b
⊎-dual-×-from∘to ¬a⊎b = extensionality λ a⊎b → ⊥-elim (¬a⊎b a⊎b) 

⊎-dual-×-to∘from : ∀ {A B : Set} (x : (¬ A) × (¬ B)) → ⊎-dual-×-to (⊎-dual-×-from x) ≡ x
⊎-dual-×-to∘from _ = refl

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record {
  to = ⊎-dual-×-to ;
  from =  ⊎-dual-×-from ; 
  from∘to = ⊎-dual-×-from∘to ;
  to∘from = ⊎-dual-×-to∘from
  }
\end{code}

#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

\begin{code}
postulate
  exclude-middle : ∀ {A : Set} → A ⊎ ¬ A

⊎-elim : ∀ {A B C : Set} → (A ⊎ B) → (A → C) → (B → C) → C
⊎-elim (inj₁ a) ac _ = ac a
⊎-elim (inj₂ b) _ bc = bc b

to-dec : (A : Set) → Dec A
to-dec a = ⊎-elim exclude-middle (λ z → z) λ z → no (λ z₁ → z (yes z₁))

double-negation : ∀ {A : Set} → ¬ ¬ A → A
double-negation {a} with to-dec a
double-negation | yes a = λ _ → a
double-negation | no ¬a = λ ¬¬a → ⊥-elim (¬¬a ¬a)

pierce-law : ∀ {A B : Set} → ((A → B) → A) → A
pierce-law {a} {b} f with to-dec a
pierce-law _ | yes a = a
pierce-law {a} {b} f | no ¬p with to-dec b
pierce-law f | no ¬a | yes b = f (λ _ → b)
pierce-law f | no ¬a | no ¬b = f λ a → ⊥-elim (¬a a)

imp-disj : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
imp-disj {a} {b} ab with to-dec a
imp-disj ab | yes p = inj₂ (ab p)
imp-disj ab | no ¬p = inj₁ ¬p

de-morgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
de-morgan {a} {_} ab with to-dec a
de-morgan ab | yes a = inj₁ a
de-morgan {_} {b} ab | no ¬p with to-dec b
de-morgan ab | no ¬a | yes b = inj₂ b
de-morgan ab | no ¬a | no ¬b = ⊥-elim (ab ⟨ ¬a , ¬b ⟩)
\end{code}


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
\begin{code}
Stable : Set → Set
Stable A = (¬ ¬ A) → A
\end{code}
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

\begin{code}
neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable f a = f (λ z → z a)

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable sa sb sa×b = ⟨ sa (λ z → sa×b (λ z₁ → z (proj₁ z₁))) , sb (λ z → sa×b (λ z₁ → z (proj₂ z₁))) ⟩
\end{code}

## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

\begin{code}
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record {
  to = λ f → ⟨ (λ a → proj₁ (f a)) , (λ a → proj₂ (f a)) ⟩ ;
  from = λ f a → ⟨ (proj₁ f a) , (proj₂ f a) ⟩ ;
  from∘to = λ x → refl ;
  to∘from = λ y → refl
  }
\end{code}

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
Does the converse hold? If so, prove; if not, explain why.

\begin{code}
⊎∀-implies-∀⊎ : ∀ {A : Set} { B C : A → Set } →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ f a = ⊎-elim f (λ x → inj₁ (x a)) λ z → inj₂ (z a)
\end{code}

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.

\begin{code}
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

-- ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
--   ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
-- ∃-distrib-⊎ = record {
--   to = λ y → ∃-elim (λ a B⊎C → ⊎-elim B⊎C (λ Ba → inj₁ ⟨ a , Ba ⟩) λ z → inj₂ ⟨ a , z ⟩) y ;
--   from = λ B⊎C → ⊎-elim B⊎C (λ ∃B → ∃-elim (λ x x₁ → ⟨ x , inj₁ x₁ ⟩) ∃B) λ ∃C → ∃-elim (λ x z → ⟨ x , inj₂ z ⟩) ∃C  ; 
--   from∘to = λ x → {!!} ;
--   to∘from = λ y → {!!}
--   }
\end{code}

#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
Does the converse hold? If so, prove; if not, explain why.

\begin{code}
∃×-implies-×∃ : ∀ {A : Set} { B C : A → Set } →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ f = ⟨ (∃-intro f (λ x x₁ → proj₁ x₁)) , (∃-intro f (λ x → proj₂)) ⟩
\end{code}

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

\begin{code}
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

eq³ : ∀ {m} → suc (m * 2) ≡ m + (m + zero) + 1
eq³ {m} = begin
    suc (m * 2)
  ≡⟨ +-comm 1 (m * 2) ⟩
  m * 2 + 1
  ≡⟨ cong (λ x → x + 1) (
  begin
  m * 2
  ≡⟨ *-comm m 2 ⟩
  m + (m + zero)
  ∎
  ) ⟩
    m + (m + zero) + 1
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

∃-even¹ : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd¹  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even¹ ⟨  zero , refl ⟩  =  even-zero
∃-even¹ ⟨ suc m , refl ⟩  =  even-suc (∃-odd¹ ⟨ m , refl ⟩)

∃-odd¹  ⟨     m , refl ⟩  =  odd-suc (∃-even¹ ⟨ m , refl ⟩)


∃-even : ∀ {n : ℕ} → ∃[ m ] ( 2 * m  ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] ( 2 * m + 1  ≡ n) → odd n

∃-even ⟨ m , refl ⟩ = ∃-even¹ ⟨ m , *-comm m 2 ⟩

∃-odd ⟨ m , refl ⟩ = ∃-odd¹ ⟨ m , eq³ {m} ⟩
\end{code}

#### Exercise `∃-+-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

\begin{code}
∃-+-≤-suc : ∀ {y z : ℕ} → (∃[ x ] (x + y ≡ z)) → ∃[ x ] (suc x + y ≡ suc z)
∃-+-≤-suc f = ∃-intro f λ x x₁ → cong suc x₁

∃-+-≤ʳ : ∀ {y z : ℕ} → y ≤ z → (∃[ x ] (x + y ≡ z))
∃-+-≤ʳ {zero} {zero} _ = ⟨ zero , refl ⟩
∃-+-≤ʳ {zero} {suc z} z≤n =  ⟨ suc z , cong suc (+-identityʳ z) ⟩
∃-+-≤ʳ {suc y} {(suc n)} (s≤s y≤z) = ∃-intro (∃-+-≤ʳ y≤z) λ x x+y≡n →
  begin
    x + suc y
  ≡⟨ +-comm x (suc y) ⟩
    suc (y + x)
  ≡⟨ cong suc (+-comm y x) ⟩ 
    suc (x + y)
   ≡⟨ cong suc x+y≡n ⟩
    suc n
  ∎
\end{code}

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
Does the converse hold? If so, prove; if not, explain why.

\begin{code}
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ f = ∃-elim (λ x x₁ x₂ → x₁ (x₂ x)) f
\end{code}

#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers.

    data Bin : Set where
      nil : Bin
      x0_ : Bin → Bin
      x1_ : Bin → Bin

And ask you to define the following functions and predicates.

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties.

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.

\begin{code}

-- can-isomorph :
--     {Can : Bin → Set}
--   → {from : Bin → ℕ}
--   → {to : ℕ → Bin}
--   → {eq : {n : ℕ} → from (to n) ≡ n}
--   → {from∘to : {n : ℕ} → Can (to n)}
--   → {to∘from : {b : Bin} → Can b → to (from b) ≡ b}
--   → (∃[ x ] Can x) ≃ ℕ
-- can-isomorph {can} {from} {to} {eq} {from∘to} {to∘from} =
--   record {
--   to = λ f → ∃-elim (λ x _ → from x) f ;
--   from = λ n → ⟨ (to n) , from∘to ⟩ ;
--   from∘to = λ f → ∃-elim (λ b canb → {!!}) f ;
--   to∘from = λ y → eq
--   }


\end{code}


## Decidable

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality.
\begin{code}
suc-inv : ∀ {m n : ℕ} → suc m < suc n → m < n
suc-inv (s<s smsn) = smsn

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no λ ()
zero <? suc n = yes z<s
suc m <? zero = no (λ ())
suc m <? suc n with m <? n
(suc m <? suc n) | yes p = yes (s<s p)
(suc m <? suc n) | no ¬p = no λ sm<sn → ⊥-elim (¬p (suc-inv sm<sn))
\end{code}

#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
\begin{code}
_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
(suc m ≡ℕ? suc .m) | yes refl = yes refl
(suc m ≡ℕ? suc n) | no ¬p = no λ sm≡sn → ¬p (cong-inv sm≡sn)
  where
    cong-inv : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    cong-inv refl = refl
\end{code}


#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
\begin{code}
postulate
  ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
  ∨-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
  not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
\end{code}
  
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from 
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
\begin{code}
_iff_ : Bool → Bool → Bool
false iff false = true
false iff true = false
true iff b = b

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes p ⇔-dec yes p₁ = yes (record { to = λ _ → p₁ ; from = λ _ → p })
yes p ⇔-dec no ¬p = no (λ z → ¬p (to z p))
no ¬p ⇔-dec yes p = no (λ z → ¬p (from z p))
no ¬p ⇔-dec no ¬p₁ = yes (record { to = λ x → ⊥-elim (¬p x) ; from = λ x → ⊥-elim (¬p₁ x) })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋  
iff-⇔ (yes p) (yes p₁) = refl
iff-⇔ (yes p) (no ¬p) = refl
iff-⇔ (no ¬p) (yes p) = refl
iff-⇔ (no ¬p) (no ¬p₁) = refl
\end{code}

