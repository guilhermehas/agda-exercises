---
title     : "Assignment1: PUC Assignment 1"
layout    : page
permalink : /Assignment1/
---

\begin{code}
module Assignment1 where
\end{code}

Guilherme Horta Alvares da Silva
guilhermehas@hotmail.com

## Introduction

<!-- This assignment is due **1pm Friday 26 April**. -->

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
open import Data.Empty using (⊥)
open import Data.Bool
open import Data.Empty.Irrelevant using (⊥-elim)
open import plfa.Relations using (_<_; z<s; s<s; zero; suc; even; odd)
\end{code}

## Naturals

#### Exercise `seven` {#seven}

Write out `7` in longhand.

\begin{code}
example7 : 7 ≡ (suc (suc (suc (suc (suc (suc (suc zero)))))))
example7 = refl
\end{code}

#### Exercise `+-example` {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

\begin{code}
+-example : 3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎
\end{code}

#### Exercise `*-example` {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.

\begin{code}
*-example : 3 * 4 ≡ 12
*-example =
  begin
    3 * 4
  ≡⟨⟩
    3 + (3 * 3)
  ≡⟨⟩
    3 + (3 + (2 * 3))
  ≡⟨⟩
    3 + (3 + (3 + (1 * 3)))
  ≡⟨⟩
    3 + (3 + (3 + (3 + (0 * 3))))
  ≡⟨⟩
    12
  ∎
\end{code}

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.

\begin{code}
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)
\end{code}

#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

\begin{code}
∸-examples-1 : 5 ∸ 3 ≡ 2
∸-examples-1 =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2
  ∎

∸-examples-2 : 3 ∸ 5 ≡ 0
∸-examples-2 =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0
  ∎
\end{code}

#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
\begin{code}
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
\end{code}
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

\begin{code}
inc : Bin → Bin
inc nil = nil
inc (x0 n) = x1_ n
inc (x1 nil) = x0 x1 nil
inc (x1 (x0 n)) = x0 x1 (inc n)
inc (x1 (x1 n)) = x0 (inc (x1 n))

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 2 * from n + 1

to : ℕ → Bin
to zero = x0_ nil
to (suc n) = inc (to n)
\end{code}

## Induction

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

```
  The XOR operator with distributivity with multiplication.
```

Give an example of an operator that has an identity and is
associative but is not commutative.

```
  In matrix multiplication. The operator * is associativity A*(B*C) = (A*B)*C, has identity I. But A*B ≠ B*A. ‌
```

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]

```
-- On the first day, we know about associativity of 0.
(0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (4 + 0) + 5 ≡ 4 + (0 + 5)   ...

-- On the second day, we know about associativity of 0 and 1.
(0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (4 + 0) + 5 ≡ 4 + (0 + 5)   ...
(0 + 1) + 0 ≡ 0 + (1 + 0)   ...   (4 + 1) + 5 ≡ 4 + (1 + 5)   ...

-- On the third day, we know about associativity of 0, 1, and 2.
(0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (4 + 0) + 5 ≡ 4 + (0 + 5)   ...
(0 + 1) + 0 ≡ 0 + (1 + 0)   ...   (4 + 1) + 5 ≡ 4 + (1 + 5)   ...
(0 + 2) + 0 ≡ 0 + (2 + 0)   ...   (4 + 2) + 5 ≡ 4 + (2 + 5)   ...


```

#### Exercise `+-swap` (recommended) {#plus-swap} 

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

\begin{code}
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
\end{code}


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

\begin{code}
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
\end{code}

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

\begin{code}
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
\end{code}

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

\begin{code}
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
\end{code}

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

\begin{code}
0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl
\end{code}

#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

\begin{code}
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero zero p = refl
∸-+-assoc zero (suc n) zero = refl
∸-+-assoc zero (suc n) (suc p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) zero = ∸-+-assoc m n zero
∸-+-assoc (suc m) (suc n) (suc p) = ∸-+-assoc m n (suc p)
\end{code}

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.

\begin{code}
exampleNotToFrom : to (from (x0 x0 nil)) ≡ (x0 x0 nil) → ⊥
exampleNotToFrom ()

inc-nil : ∀ {b : Bin} → inc b ≡ nil → b ≡ nil
inc-nil {nil} refl = refl
inc-nil {x0 b} ()
inc-nil {x1 nil} ()
inc-nil {x1 (x0 b)} ()
inc-nil {x1 (x1 b)} ()

to-nil-absurd : ∀ {b : Bin} {n : ℕ} → b ≡ to n → b ≡ nil → ⊥
to-nil-absurd {.(x0 nil)} {zero} refl ()
to-nil-absurd {.(inc (to n))} {suc n} refl eq = to-nil-absurd {to n} {n} refl (inc-nil {to n} eq)

-- nat-inj-helper : ∀ {x : Bin} {n : ℕ} → x ≡ to n →  from (inc x) ≡ suc (from x)
-- nat-inj-helper {nil} {zero} ()
-- nat-inj-helper {nil} {suc n} eq = ⊥-elim (to-nil-absurd refl (inc-nil {to n} (sym eq )))
-- nat-inj-helper {x0 x} {n} eq = {!!}
-- nat-inj-helper {x1 nil} {n} eq = {!!}
-- nat-inj-helper {x1 (x0 x)} {n} eq = {!!}
-- nat-inj-helper {x1 (x1 x)} {n} eq = {!!}

-- natInject : ∀ {n ∶ ℕ} → from (to n) ≡ n
-- natInject {zero} = refl
-- natInject {suc n} = {!!}

\end{code}

## Relations


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

\begin{code}
data _≤b_ : Bool → Bool → Set where
  all : (b₁ b₂ : Bool) → b₁ ≤b b₂

≤b-refl : ∀ {n : Bool} → n ≤b n
≤b-refl {n} = all n n

≤b-trans : ∀ {m n p : Bool} → m ≤b n → n ≤b p → m ≤b p
≤b-trans {m} {_} {p} _ _ = all m p

not-≤b-symm : ∀ {m n : Bool} → m ≡ false → n ≡ true → m ≤b n → n ≤b m → m ≡ n → ⊥
not-≤b-symm {false} {.false} refl () m<n n<m refl
\end{code}

Give an example of a partial order that is not a preorder.

```
  It is impossible because all partial order is a preoder
```

#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

```
  In the case that (s≤s m≤n), we have .m = suc m and .n = suc n. In the second argument, it will be suc n ≤ suc m. The constructor z≤z is impossible, because zero is not suc n and is not suc m.
```

#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

\begin{code}
*-mono-≤ : ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
  -------------
  → m * p ≤ n * q

*-mono-≤ z≤n p≤q = z≤n
*-mono-≤ {suc m} {suc n} {p} {q} (s≤s m≤n) p≤q = +-mono-≤ p≤q (*-mono-≤ m≤n p≤q)
\end{code}

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

\begin{code}
<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
\end{code}

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

\begin{code}
data Ordering : ℕ → ℕ → Set where
  less : {m n : ℕ} → .(m < n) → Ordering m n
  equal : {m n : ℕ} → .(m ≡ n) → Ordering m n
  greater : {m n : ℕ} → .(n < m) → Ordering m n

≡-same : ∀ {m n : ℕ} → m ≡ n → n ≡ m
≡-same refl = refl

<-≡-disjoint : ∀ {m n} → (m < n) → (m ≡ n) → ⊥
<-≡-disjoint (s<s m<n) refl = <-≡-disjoint m<n refl

<->-disjoint : ∀ {m n} → (m < n) → (n < m) → ⊥
<->-disjoint z<s ()
<->-disjoint (s<s m<n) (s<s n<m) = <->-disjoint m<n n<m

trichotomy : ∀ {m n : ℕ} → (x : Ordering m n) → (y : Ordering m n) → x ≡ y
trichotomy (less x) (less y) = refl
trichotomy (less x) (equal y) = ⊥-elim (<-≡-disjoint x y)
trichotomy (less x) (greater y) = ⊥-elim  (<->-disjoint x y)
trichotomy (equal x) (less y) = ⊥-elim  (<-≡-disjoint y x)
trichotomy (equal x) (equal y) = refl
trichotomy (equal x) (greater y) = ⊥-elim  (<-≡-disjoint y (≡-same x))
trichotomy (greater x) (less y) = ⊥-elim  (<->-disjoint y x)
trichotomy (greater x) (equal y) = ⊥-elim (<-≡-disjoint x (≡-same y))
trichotomy (greater x) (greater y) = refl
\end{code}

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

\begin{code}
eq-< : ∀ (m n p : ℕ) → n ≡ p → m < n → m < p
eq-< m n .n refl m<n = m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  ---------------
  → m + p < n + q
+-mono-< zero zero p q m<n p<q = p<q
+-mono-< zero (suc n) zero q m<n p<q = z<s
+-mono-< zero (suc n) (suc p) (suc q) z<s (s<s p<q) = s<s (eq-< p (suc n + q) (n + suc q) (sym (+-suc n q)) (+-mono-< zero (suc n) p q z<s p<q) )
+-mono-< (suc m) zero p q () p<q
+-mono-< (suc m) (suc n) p q (s<s m<n) p<q = s<s (+-mono-< m n p q m<n p<q)
\end{code}

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

\begin{code}
≤-iff-<ʳ : {m n : ℕ} → suc m ≤ n → m < n
≤-iff-<ʳ {zero} {.(suc _)} (s≤s m<n) = z<s
≤-iff-<ʳ {suc m} {.(suc _)} (s≤s m<n) = s<s (≤-iff-<ʳ m<n)

≤-iff-<ˡ : {m n : ℕ}  → m < n → suc m ≤ n
≤-iff-<ˡ z<s = s≤s z≤n
≤-iff-<ˡ (s<s m<n) = s≤s (≤-iff-<ˡ m<n)
\end{code}

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

\begin{code}
<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited {zero} {.(suc _)} {.(suc _)} z<s (s<s n<p) = z<s
<-trans-revisited {suc m} {.(suc _)} {zero} (s<s m<n) ()
<-trans-revisited {suc m} {.1} {suc .(suc _)} (s<s ()) (s<s z<s)
<-trans-revisited {suc .0} {.(suc (suc _))} {suc .(suc _)} (s<s z<s) (s<s (s<s n<p)) = s<s z<s
<-trans-revisited {suc .(suc _)} {.(suc (suc _))} {suc .(suc _)} (s<s (s<s m<n)) (s<s (s<s n<p)) = s<s (s<s (<-trans-revisited m<n n<p))
\end{code}

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

\begin{code}
e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
  -----------
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  → even (m + n)

e+o≡o zero on = on
e+o≡o (suc em) on = suc (o+o≡e em on)

o+o≡e (suc em) on = suc (e+o≡o em on)
\end{code}

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
