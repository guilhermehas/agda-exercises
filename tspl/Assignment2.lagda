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
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
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
\begin{code}
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩
\end{code}

Does the converse hold? If so, prove; if not, give a counterexample.

## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.


#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, give a variant that does hold.


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
\begin{code}
Stable : Set → Set
Stable A = ¬ ¬ A → A
\end{code}
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
\begin{code}
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
\end{code}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
\begin{code}
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} { B C : A → Set } →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
\end{code}
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
\begin{code}
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
\end{code}

#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
\begin{code}
postulate
  ∃×-implies-×∃ : ∀ {A : Set} { B C : A → Set } →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
\end{code}
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-+-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
\begin{code}
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
\end{code}
Does the converse hold? If so, prove; if not, explain why.


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


## Decidable

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality.
\begin{code}
postulate
  _<?_ : ∀ (m n : ℕ) → Dec (m < n)
\end{code}

#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
\begin{code}
postulate
  _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
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
postulate
  _iff_ : Bool → Bool → Bool
  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋  
\end{code}
