---
title     : "Assignment3: TSPL Assignment 3"
layout    : page
permalink : /Assignment3/
---

\begin{code}
module Assignment3 where
\end{code}

## Name
Guilherme Horta Alvares da Silva

## Email
guilhermehas@hotmail.com

## Introduction

<!-- This assignment is due **4pm Thursday 1 November** (Week 7). -->

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
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-comm; +-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Algebra.Structures using (IsMonoid)
open import Level using (Level)
open import Relation.Unary using (Decidable)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning
open import plfa.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_; ++-assoc)
open import plfa.Lambda hiding (begin_; _∎; ƛ′_⇒_; case′_[zero⇒_|suc_⇒_]; μ′_⇒_; plus′)
open import plfa.Properties hiding (value?; unstuck; preserves; wttdgs)
\end{code}

#### Exercise `reverse-++-commute` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first.
\begin{code}
reverse-++-commute : ∀ {A : Set} {xs ys : List A}
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

reverse-++-commute {_} {[]} {[]} = refl
reverse-++-commute {_} {[]} {x ∷ ys} = list++[] (reverse ys ++ [ x ])
  where
    list++[] : ∀ {A : Set} (xs : List A)
      → xs ≡ xs ++ []
    list++[] [] = refl
    list++[] (x ∷ xs) = cong (λ ys → x ∷ ys) (list++[] xs)
reverse-++-commute {_} {x ∷ xs} {ys} =
  begin
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong  (λ ys → ys ++ [ x ]) (reverse-++-commute {_} {xs} {ys}) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ∎
\end{code}

#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution.
\begin{code}
reverse-involutive : ∀ {A : Set} {xs : List A}
  → reverse (reverse xs) ≡ xs
reverse-involutive {_} {[]} = refl
reverse-involutive {_} {x ∷ xs} = 
  begin
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-commute {_} {reverse xs} {[ x ]} ⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (_∷_ x) reverse-involutive ⟩
    x ∷ xs
  ∎
\end{code}

#### Exercise `map-compose`

Prove that the map of a composition is equal to the composition of two maps.
\begin{code}
map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-compose = extensionality λ ys → helper ys
  where
    helper : ∀ {A B C : Set} {f : A → B} {g : B → C} (xs : List A)
      → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    helper [] = refl
    helper {_} {_} {_} {f} {g} (x ∷ xs) = cong (_∷_ (g (f x))) (helper xs)
\end{code}
The last step of the proof requires extensionality.

#### Exercise `map-++-commute`

Prove the following relationship between map and append.
\begin{code}
map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
  →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute {_} {_} {f} {[]} {ys} = refl
map-++-commute {_} {_} {f} {x ∷ xs} {ys} = cong (_∷_ (f x)) (map-++-commute {_} {_} {f} {xs} {ys})
\end{code}

#### Exercise `map-Tree`

Define a type of trees with leaves of type `A` and internal
nodes of type `B`.
\begin{code}
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
\end{code}
Define a suitabve map operator over trees.
\begin{code}
map-Tree : ∀ {A B C D : Set}
  → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree ac bd (leaf root) = leaf (ac root)
map-Tree ac bd (node left root right) = node (map-Tree ac bd left) (bd root) (map-Tree ac bd right)
\end{code}

#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example,

    product [ 1 , 2 , 3 , 4 ] ≡ 24

\begin{code}
product : List ℕ → ℕ
product [] = 1
product (x ∷ xs) = x * product xs
\end{code}

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows.
\begin{code}
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ op e [] ys = refl
foldr-++ op e (x ∷ xs) ys = cong (op x) (foldr-++ op e xs ys)
\end{code}


#### Exercise `map-is-foldr`

Show that map can be defined using fold.
\begin{code}
map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr = extensionality λ xs → helper xs
  where
    helper : ∀ {A B : Set} {f : A → B}  → (xs : List A) →
      map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    helper [] = refl
    helper {_} {_} {f} (x ∷ xs) = cong (_∷_ (f x)) (helper xs)
\end{code}
This requires extensionality.

#### Exercise `fold-Tree`

Define a suitable fold function for the type of trees given earlier.
\begin{code}
fold-Tree : ∀ {A B C : Set}
  → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree ac cbc (leaf root) = ac root
fold-Tree ac cbc (node left root right) = cbc (fold-Tree ac cbc left) root (fold-Tree ac cbc right)
\end{code}

#### Exercise `map-is-fold-Tree`

Demonstrate an anologue of `map-is-foldr` for the type of trees.

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows.
\begin{code}
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
\end{code}
For example,
\begin{code}
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
\end{code}
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`.
\begin{code}
solve¹ : ∀ (n : ℕ) → n * 2 + n * (n ∸ 1) ≡ n + n * n
solve¹ zero = refl
solve¹ (suc n) = cong suc (
  begin
      suc (n * 2 + (n + n * n))
    ≡⟨ cong (λ x → suc (x + (n + n * n))) (*-comm n 2) ⟩
      suc (n + (n + zero) + (n + n * n))
    ≡⟨ cong (λ x → suc (n + x + (n + n * n))) (+-comm n zero) ⟩
      suc (n + n + (suc n * n))
    ≡⟨ cong (λ x → suc (n + n + x)) (*-comm (suc n) n) ⟩
      suc (n + n + n * suc n)
    ≡⟨ cong (λ x → suc x) (+-assoc n n (n * suc n)) ⟩
      suc (n + (n + n * suc n))
    ≡⟨ cong (λ x → x + (n + n * suc n)) (+-comm 1 n) ⟩
      n + 1 + (n + n * suc n)
    ≡⟨ +-assoc n 1 (n + n * suc n) ⟩
      n + suc (n + n * suc n)
  ∎)

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) = 
  begin
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    n * 2 + (sum (downFrom n)) * 2
  ≡⟨ cong (λ x → n * 2 + x) (sum-downFrom n) ⟩
    n * 2 + (n * (n ∸ 1))
  ≡⟨ solve¹ n ⟩
    n + n * n
  ∎
\end{code}


#### Exercise `foldl`

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example,

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

\begin{code}
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl f e [] = e
foldl f e (x ∷ xs) = foldl f (f e x) xs
\end{code}

#### Exercise `foldr-monoid-foldl`

Show that if `_⊕_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

\begin{code}
foldl-monoid : ∀ {A : Set} {ε : A} {_⊕_ : A → A → A} (x y : A) (xs : List A)
  → (IsMonoid _≡_ _⊕_ ε)
  → x ⊕ foldl _⊕_ y xs ≡ foldl _⊕_ (x ⊕ y) xs
foldl-monoid {_} {ε} {_⊕_} x y [] isMonoid = refl
foldl-monoid {_} {ε} {_⊕_} x y (z ∷ zs) isMonoid = 
  begin
    (x ⊕ foldl _⊕_ (y ⊕ z) zs)
  ≡⟨ foldl-monoid {_} {ε} {_⊕_} x (y ⊕ z) zs isMonoid ⟩
    foldl _⊕_ (x ⊕ (y ⊕ z)) zs
  ≡⟨ cong (λ u → foldl _⊕_ u zs) (Eq.sym (assoc x y z)) ⟩
    foldl _⊕_ ((x ⊕ y) ⊕ z) zs
  ∎
  where
    open IsMonoid isMonoid

foldr-monoid-foldl : ∀ {A : Set} {ε : A} {_⊕_ : A → A → A} (xs : List A) → (IsMonoid _≡_ _⊕_ ε) → foldr _⊕_ ε xs ≡ foldl _⊕_ ε xs
foldr-monoid-foldl [] monoid = refl
foldr-monoid-foldl {_} {ε} {_⊕_} (x ∷ xs) isMonoid = 
  begin
    (x ⊕ (foldr _⊕_ ε xs))
  ≡⟨ cong (λ y → x ⊕ y) (foldr-monoid-foldl xs isMonoid) ⟩
  (x ⊕ foldl _⊕_ ε xs)
  ≡⟨ foldl-monoid x ε xs isMonoid ⟩
    foldl _⊕_ (x ⊕ ε) xs
  ≡⟨ Eq.cong (λ w → foldl _⊕_ w xs) change-ε ⟩
    foldl _⊕_ (ε ⊕ x) xs
  ∎
  where
    open IsMonoid isMonoid
    change-ε : x ⊕ ε ≡ ε ⊕ x
    change-ε = 
      begin
        x ⊕ ε
      ≡⟨ identityʳ x ⟩
        x
      ≡⟨ Eq.sym (identityˡ x) ⟩
        (ε ⊕ x)
      ∎
\end{code}

#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-↔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.


#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.


#### Exercise `¬Any≃All¬` (stretch)

First generalise composition to arbitrary levels, using
[universe polymorphism][plfa.Equality#unipoly].
\begin{code}
_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)
\end{code}

Show that `Any` and `All` satisfy a version of De Morgan's Law.
\begin{code}
postulate
  ¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
\end{code}

Do we also have the following?
\begin{code}
postulate
  ¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ All P) xs ≃ Any (¬_ ∘′ P) xs
\end{code}
If so, prove; if not, explain why.


#### Exercise `any?` (stretch)

Just as `All` has analogues `all` and `all?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `any?` which determine whether a predicates holds
for some element of a list.  Give their definitions.


#### Exercise `filter?` (stretch)

Define the following variant of the traditional `filter` function on lists,
which given a list and a decidable predicate returns all elements of the
list satisfying the predicate.
\begin{code}
postulate
  filter? : ∀ {A : Set} {P : A → Set}
    → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
\end{code}


## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.


#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
\begin{code}
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}
The definition of `plus` can now be written as follows.
\begin{code}
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
\end{code}
Write out the definition of multiplication in the same style.

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.


#### Exercise `—↠≃—↠′`

Show that the two notions of reflexive and transitive closure
above are isomorphic.


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.


## Properties


#### Exercise `Progress-≃`

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.


#### Exercise `progress′`

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.


#### Exercise `value?`

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value.
\begin{code}
postulate
  value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
\end{code}


#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.


#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.


#### Exercise: `progress-preservation`

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.


#### Exercise `subject-expansion`

We say that `M` _reduces_ to `N` if `M —→ N`,
and conversely that `M` _expands_ to `N` if `N —→ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.


#### Exercise `stuck`

Give an example of an ill-typed term that does get stuck.


#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.








