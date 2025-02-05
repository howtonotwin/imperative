<!--
```agda
{-# OPTIONS --allow-unsolved-metas --guardedness #-}
module Exposition where

open import Agda.Primitive

open import Data.List
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality
```
-->
Review
===

This project defines a sublanguage for verified imperative programming in the
dependently typed functional language Agda. The goals are to achieve a design
that is simple and (relatively) easy to use while being sufficiently general to
allow "any" imperative algorithm to be expressed.

In some existing approaches towards the verification of imperative programs, the
imperative program is written in a traditional imperative programming language
and then imported as data into a theorem proving system. For example, the
Verified Software Toolchain project relies on a C compiler that, in addition to
compiling C code to machine code, also outputs Coq files containing a
representation of the C syntax tree(s). A library in the theorem prover can then
provide a way to specify and prove properties of programs in the imperative
language (as imported as data structures in the theorem prover). While this
approach works, it enforces a strict separation between imperative code and
proofs of correctness. Indeed, the code and the proofs will usually be written
in two different languages. Consequences of such an approach include the need to
account for corner cases in the semantics of "basic" constructs in the
imperative language, which often results in the generation of tedious proof
obligations.

The Curry-Howard correspondence suggests that a strict distinction between code
and proof is not necessary. Indeed, the functional programming paradigm is
readily compatible with dependent types, which are rich and strong enough to
express and enforce programmer-specified invariants on data structures. For
example, with the appropriate definitions, one may write in Agda a function

~~~agda
sorted : (xs : List ℕ) → Σ[ ys ∈ List ℕ ] Permutation xs ys × Sorted ys
~~~

The type of such a function declares that it takes lists of natural numbers to
*sorted* lists of natural numbers such that each output list is a permutation of
the corresponding input list. It is further possible to define `sorted` without
strictly separating the "code" part from the "proof" part: the Curry-Howard
correspondence says that proofs have the same structure as code, so they can
both be written in the same language and even be interspersed.

Another viewpoint on the separation of code and proof appears in the language
[Xanadu], which is an imperative language specifically designed to support
dependent typing. An interesting feature of Xanadu is that it separates what it
calls "reference variables", which represent mutable memory locations, from
"value variables", which represent immutable values read or written from memory
locations. This belies a fundamental tension between dependent typing and
imperative programming: in a dependently typed system, the type of a variable
may refer to the values of other variables, but, in an imperative language, the
value of a given variable may change over the course of execution. When these
features are combined, the question arises: what should happen when a variable
that appears in the type of another variable changes value? Somehow, the
variable with the dependent type must be invalidated (a new value matching the
conforming to the new type must be demanded). Alternatively, there must be some
way to refer to the old value of the changing variable so that types that depend
on it remain valid. Both Xanadu and VST take the second approach: they create
some kind of separation between mutable references and immutable values, and
enforce that types and propositions may only depend on values. (In Xanadu, the
distinction is built into the language. In VST, variables in C code may be
mutable while variables in Coq code never are). To express that the type of a
variable depends on a mutable variable, an immutable variable that represents
the *current* value of the mutable variable is introduced, and the dependent
variable depends on this immutable variable. If the mutable variable is changed,
the type and value of the dependent variable can then stay the same. If the
dependent variable is mutable, it can later be reassigned a new value whose type
matches the new value of the dependency.

The seemingly necessary separation of mutable references from immutable values
in verified imperative programming is strongly reminiscent of Haskell's
[`Control.Monad.ST`][ST] facility. Haskell, despite being a pure and functional
language, supports imperative subprograms via `ST`. Imperative programs in `ST`
have access to mutable references, but such references are not ordinary Haskell
variables. Instead, references may be read to bind their current value to an
immutable variable and the value of a pure expression may be written to a
reference. Haskell also provides a *pure* function `runST` from imperative
programs to their return values. It is possible for `runST` to be pure because
its type ensures that the imperative subprogram passed to it cannot depend on or
change any state outside the subprogram. Thus imperative subprograms in `ST` can
freely interoperate with pure functional code.

All of the above considerations suggest the following design: in Agda, a
dependently typed functional programming language that compiles to Haskell, it
should be possible to define an interface to Haskell's `ST` that refines the
type of imperative programs to include their specifications. As Agda variables
are immutable, it should be safe to allow specifications and types to depend on
them. Mutable references are to be represented by values of some opaque data
type that can be read or written within imperative subprograms. (A similar
approach is taken in the work [Ynot], which uses Coq instead. This work was
originally developed independently of Ynot and has some important differences).

[Xanadu]: https://doi.org/10.1109/LICS.2000.855785
[Ynot]: https://github.com/ynot-harvard/ynot
[ST]: https://hackage.haskell.org/package/base-4.20.0.1/docs/Control-Monad-ST.html

Design
===
To begin, the core signature of `Control.Monad.ST` in Haskell is

~~~haskell
type ST :: Type -> Type -> Type
runST   :: (forall s. ST s a) -> a
return  :: a -> ST s a
(>>=)   :: ST s a -> (a -> ST s b) -> ST s b

type STRef :: Type -> Type -> Type
newSTRef   ::              a -> ST s (STRef s a)
readSTRef  :: STRef s a      -> ST s a
writeSTRef :: STRef s a -> a -> ST s ()
~~~

An imperative program is a value of type `ST s a`, where the type `s` represents
the "state thread" and `a` is the type of the value returned by the program.
`runST` conceptually creates a state thread `s` and passes it to a user-defined
function that is required to return an `ST s a`. (Thus, a program cannot read or
write `STRef`s created by a different use of `runST`, since the state thread of
such references will never be proven equal to the state thread provided by
`runST`.) `return x` is a trivial program that accesses no state and immediately
returns the value of the pure expression `x`. `p >>= q` is a composition of
imperative programs: it runs `p` to get a return value `x`, applies the pure
function `q` to compute a program `q x`, then runs `q x` (returning its result).

A value `r :: STRef s a` is a reference to a mutable cell accessible from state
thread `s` that always holds a (immutable) value of type `a`. `newSTRef x` is a
simple program that creates a new mutable cell initially holding `x :: a` and
returns a reference to the cell. `readSTRef r` is a program that returns (a copy
of) the value in the mutable cell pointed to be `r`, while `writeSTRef r x` is a
program that writes the value `x` to the cell represented by `r`.

A First Pass
---
```agda
module FirstPass where
```

To create an interface to `ST` usable from Agda, the first step is to decide on
an appropriate signature of types and basic operations. The signature can later
be implemented by telling Agda how to compile each declared name to Haskell
code. To start, directly lifting `ST`'s signature to Agda is simple (no changes
except syntactic adaptions and replacing Haskell's `Type` with Agda's `Set`).

```agda
  postulate
    ST     : Set → Set → Set
    runST  : ∀ {A}     → ({s : Set} → ST s A) → A
    return : ∀ {s A}   → A → ST s A
    _>>=_  : ∀ {s A B} → ST s A → (A → ST s B) → ST s B

    STRef      : Set → Set → Set
    newSTRef   : ∀ {s A} →             A → ST s (STRef s A)
    readSTRef  : ∀ {s A} → STRef s A     → ST s A
    writeSTRef : ∀ {s A} → STRef s A → A → ST s ⊤
```

Unfortunately, this signature is insufficient for our purposes. An `ST` defined
via these operations does not support proving things about programs written in
it. For example, there is nothing in the types above to guarantee that a
`readSTRef` returns the same value as given to a previous `newSTRef` or
`writeSTRef`. Thus, though the following function typechecks, we cannot show
that it is the identity!

```agda
  imperativeId : ∀ {A} → A → A
  imperativeId x = runST (newSTRef x >>= readSTRef)

  imperativeIdIsId : ∀ {A} (x : A) → imperativeId x ≡ x
  imperativeIdIsId x = {! stuck! !}
```

Another indication of this signature's inadequacy is that the type of the value
stored behind a reference is not allowed to change.

Adding Specifications
---
```agda
module AddingSpecifications where
```

We must refine `ST` to a type that is not just parametrized by a state thread
and a return type, but also declares a precondition and a postcondition for the
program it represents. A simple way to represent a precondition/postcondition is
as a list of "assignments", each pairing a reference to its current type and
value. (Note that this requires the type of assignments to live in a larger
universe than the storable values.) The type of references conversely loses the
parameter specifying the type of its values.

```agda
  postulate
    Ref : Set → Set -- we pick our own names now

  infix 6 _↦_
  record Assignment (s : Set) : Set₁ where
    constructor _↦_
    field
      var           : Ref s
      {contentType} : Set₀
      content       : contentType
  Condition : Set → Set₁
  Condition s = List (Assignment s)

  postulate
    Program    : (s : Set) (A : Set) → Condition s → (A → Condition s) → Set
```

A `Program s A pre post` is now to be interpreted as the type of imperative
programs that can run in the state thread `s` *when and only when* the state
satisfies `pre` (the *precondition*), that each return a value `x` of type `A`,
and leave a state satisfying `post x` (the *postcondition*). Note that the
postcondition of such a imperative program is allowed to depend (functionally)
on the value it returns. Thus a typing judgement `p : Program s A pre post` is
something like a Hoare triple `{pre} p {post}`. With this idea in mind, we can
upgrade the types of the basic operations.

```agda
    runProgram : ∀ {A}     → ({s : Set} → Program s A [] (λ _ → [])) → A
    return     : ∀ {s A}     {cond : A → Condition s} (x : A) → Program s A (cond x) cond
    _>>=_      : ∀ {s A B}   {pre : Condition s} {mid : A → Condition s} {post : B → Condition s} →
                 Program s A pre mid →
                 ((x : A) → Program s B (mid x) post) →
                 Program s B pre post

    alloc : ∀ {s} → Program s (Ref s) [] (λ r → (r ↦ tt) ∷ []) -- we fix tt : ⊤ as the initial value
    write : ∀ {s A B} (r : Ref s) {x : A} (y : B) → Program s ⊤ ((r ↦ x) ∷ []) (λ _ → (r ↦ y) ∷ [])
```

Note that we make use of a separation logic-style interpretation of pre- and
post-conditions. That means that each `Assignment` in a `Condition` is
considered to be in *separate* conjunction with all the others. If any two
`Assignments` give values to the same `Ref`, the whole `Condition` never holds
(represents an unreachable state). Relatedly, `write r y` requires `r ↦ x` in
its precondition, where `x` is the old value of `r`. Since `Assignment`s cannot
be "duplicated", this means a `write` *consumes* the information `r ↦ x`, such
that the program state afterwards (that is, the precondition of the `Program`
type expected in the hole in the expression `write r y >>= λ _ → ?`) no longer
contains `r ↦ x`.

The `read` operation is now a problem and left for later. Before we discuss
`read`, we need to add a few more basic operations that encode certain
manipulations of `Condition`s.

First, certain program states can be taken to other, syntactically different
states by performing no action at all. Allowed changes are reordering of
`Assignment`s within a `Condition` (i.e. "the exchange rule") and forgetting of
`Assignment`s (i.e. "the weakening rule", which renders the references on the
LHSes unusable; note that Agda and Haskell are garbage-collected), as well as
(automatically) replacement of expressions by equals. The allowed transitions
are encoded by the relation `Restructuring : Conditions s → Condition s → Set₁`
(definition omitted), and the program that applies a `Restructuring` called `r`
to the state is named `restructure r`.

<!--
```agda
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring {s} : Condition s → Condition s → Set₁ where
    [_]╳ : (discards : Condition s) → Restructuring discards []
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition s)
      (v : Ref s) {A} {x : A}
      (r : Condition s) {rest : Condition s} →
      Restructuring (l ++ r) rest →
      Restructuring (l ++ v ↦ x ∷ r) (v ↦ x ∷ rest)
  pattern ╳ = [ _ ]╳
  pattern ∎ = [ [] ]╳
  postulate
```
-->
```agda
    restructure : ∀ {s} {pre post : Condition s} → Restructuring pre post → Program s ⊤ pre (λ _ → post)
```

Second, while `_>>=_` is sufficient for composing imperative programs where the
postcondition of the first matches exactly with the precondition of the latter,
in general a subprogram may have to run in an environment where its precondition
holds *and* some other (separate in location!) mutable state exists. The "frame
rule" is the principle that programs can run in such environments and, moreover,
that the "extra" state is unmodified afterwards. The frame rule is represented
here as a literal function that turns programs on smaller states into programs
on larger states, but its implementation is intended to be a no-op.

```agda
    frame :
      ∀ {s A} (side : Condition s) {pre : Condition s} {post : A → Condition s} →
      Program s A pre post → Program s A (pre ++ side) (λ x → post x ++ side)
```

All that said, we return to `read` and try to come up with a type.

~~~agda
read : ∀ {s A} (r : Ref s) {x : A} → Program s ??? ((r ↦ x) ∷ []) (λ _ → (r ↦ x) ∷ [])
~~~

What should `read`'s return type (the `???`) be? Perhaps we should say `A`, but
the point of refining `ST` to `Program` was to give a more precise type:
`read r` specifically returns an `A` that we know to be equal to `x`, where `x`
is the value assigned to `r` in the precondition. We can define an auxiliary
type to represent this information.

```agda
  data Exactly {A : Set} : A → Set where
    exactly : (x : A) → Exactly x
  postulate
    read : ∀ {s A} (r : Ref s) {x : A} → Program s (Exactly x) ((r ↦ x) ∷ []) (λ _ → (r ↦ x) ∷ [])
```

But `read` is still very strange. It takes as an argument (`x`, which happens to
declared implicit) a value equal to the value it is meant to read and return.
The following would be a valid implementation. Note that it ignores the mutable
reference.

```agda
  _ : ∀ {s A} (r : Ref s) {x : A} → Program s (Exactly x) ((r ↦ x) ∷ []) (λ _ → (r ↦ x) ∷ [])
  _ = λ _ {x} → return (exactly x)
```

But we have at least achieved the goal of proving things about programs. Note
that the type of the function below states that it returns what it is given.

<!--
```agda
  _>>_ :
      ∀ {s A B}
      {pre : Condition s} {mid : A → Condition s} {post : B → Condition s} →
      Program s A pre mid → ({x : A} → Program s B (mid x) post) → Program s B pre post
  p >> q = do
    x ← p
    q {x}
```
-->
```agda
  imperativeExactly : ∀ {A} (x : A) → Exactly x
  imperativeExactly x = runProgram do
    -- Agda desugars do-notation to _>>=_ and _>>_ like Haskell; definition of _>>_ omitted
    r ← alloc
    write r x
    y ← read r
    restructure ╳ -- "forget about all live references"
    return y
```

As a more interesting example, we can define an imperative algorithm for
computing Fibonacci numbers. The natural functional definition of `fib n`
computes `O(fib n)` (i.e. exponentially many) additions when sharing is not
exploited. (Note that the type of natural numbers `ℕ` is special to Agda. Though
it looks like it uses the traditional unary representation, it actually compiles
to Haskell's `Integer`.)

```agda
  fib : ℕ → ℕ
  fib zero          = zero
  fib (suc zero)    = suc zero
  fib (suc (suc n)) = fib n + fib (suc n)
```

In an imperative language, however, Fibonacci numbers may be computed in `O(n)`
additions as in the following pseudocode (it is also possible to write an `O(n)`
version of `fib` in Agda, but that is besides the point).

~~~python
def fib(n: ℕ): ℕ
  lo = 0
  if n == 0: return lo
  n -= 1

  hi = 1
  while n != 0:
    lo, hi = hi, lo + hi
    n -= 1
  return hi
~~~

The goal is to write a definition for

```agda
  calcFib : ∀ {s} (n : ℕ) → Program s (Exactly (fib n)) [] (λ _ → [])
```

Note that the inefficient functional definition of `fib` is required to properly
state the specification of `calcFib`. Though it would be possible to simply
return a `ℕ` from `calcFib`, it would afterwards not be possible to prove
anything about that `ℕ`. (This is a difference from pure definitions, which Agda
freely computes with inside types, thus allowing properties of a definition to
be shown after the definition is made. In contrast, an imperative `Program`
needs to return a value with a rich enough type to ensure all desired properties
from the start. In this case we *completely* specify the return value of
`calcFib` by referencing an equivalent functional program.)

To actually fill in the definition of `calcFib`, start by annotating the
imperative algorithm above with a proof that it actually computes the same value
as the functional `fib`. Specifically, the program state at key points in the
program needs to be tracked.

~~~python
# returns fib n
def fib(n: ℕ): ℕ
  # let n₀ be the current value of n
  lo = 0
  if n == 0: return lo
  n -= 1

  hi = 1
  # at this point, n₀ = n + 1, lo = 0 = fib 0, hi = 1 = fib 1
  # (loop invariant) before and after each iteration,
  #   there exists an i: ℕ s.t. n₀ = n + (1 + i), lo = fib i, hi = fib (1 + i)
  # (loop entry) the loop invariant holds right before the loop with i = 0
  while n != 0:
    # at this point, for some i₀: ℕ, n₀ = n + (1 + i₀), lo = fib i₀, hi = fib (1 + i₀)
    lo, hi = hi, lo + hi
    n -= 1
    # at this point, n₀ = n + (2 + i₀), lo = fib (1 + i₀), hi = fib (2 + i₀)
    # (taking loop) the loop invariant holds at this point with i = 1 + i₀
  # (loop exit) at this point, n = 0, and the loop invariant also holds for some i: ℕ
  # hence, at this point, n₀ = 1 + i, lo = fib i, hi = fib (1 + i) = fib n₀
  return hi
  # so the return value is fib n₀ as promised
~~~

The loop body can be translated into a `Program` fragment, and the `Program`
type expresses how the loop invariant is maintained. For brevity, the
translation does not use an imperative loop with a mutable counter but simply
"unrolls" the loop with recursion.

<!--
```agda
  pure : ∀ {A} (x : A) → Exactly x
  pure = exactly
  _<*>_ : ∀ {A} {B : A → Set} {f : (x : A) → B x} {x : A} → Exactly f → Exactly x → Exactly (f x)
  exactly f <*> exactly x = exactly (f x)
  writeExactly : ∀ {s A B} {x : A} {y : B} (r : Ref s) → Exactly y → Program s ⊤ (r ↦ x ∷ []) (λ _ → r ↦ y ∷ [])
  writeExactly r (exactly y) = write r y
```
-->
```agda
  module FibBody {s} (lo hi : Ref s) where
    loopBody :
      (i : ℕ) →
      Program s ⊤
        (lo ↦ fib i ∷ hi ↦ fib (suc i) ∷ [])
        (λ _ → lo ↦ fib (suc i) ∷ hi ↦ fib (suc (suc i)) ∷ [])
    loopBody i = do
      -- the program state before and after each line of a do-block is
      -- represented by the Conditions in the Program type of the line
      -- thus the "current" and "desired" states are visible when writing a
      -- Program in the interactive Agda mode
      -- for this example, the current state is also presented in comments
      -- current state: lo ↦ fib i ∷ hi ↦ fib (suc i) ∷ []
      oldLo ← frame (hi ↦ fib (suc i) ∷ []) (read lo)
      -- current state: lo ↦ fib i ∷ hi ↦ fib (suc i) ∷ []
      restructure ([ lo ↦ fib i ∷ [] ]&[ hi ]⨾[ [] ]⨾⨾ [ [] ]&[ lo ]⨾[ [] ]⨾⨾ ∎)
      -- current state: hi ↦ fib (suc i) ∷ lo ↦ fib i ∷ []
      oldHi ← frame (lo ↦ fib i ∷ []) (read hi)
      -- current state: hi ↦ fib (suc i) ∷ lo ↦ fib i ∷ []
      -- "idiom brackets" desugar to calls to pure and _<*>_ (not shown)
      -- writeExactly unwraps Exactly before doing a write (not shown)
      -- to the eagle-eyed, yes, the following line leaks space
      frame (lo ↦ fib i ∷ []) (writeExactly hi ⦇ oldLo + oldHi ⦈)
      -- current state: hi ↦ fib (suc (suc i)) ∷ lo ↦ fib i ∷ []
      restructure ([ hi ↦ fib (suc (suc i)) ∷ [] ]&[ lo ]⨾[ [] ]⨾⨾ [ [] ]&[ hi ]⨾[ [] ]⨾⨾ ∎)
      -- current state: lo ↦ fib i ∷ hi ↦ fib (suc (suc i)) ∷ []
      frame (hi ↦ fib (suc (suc i)) ∷ []) (writeExactly lo oldHi)
      -- _ : ⊤ returned, state: lo ↦ fib (suc i) ∷ hi ↦ fib (suc (suc i)) ∷ []
```

Then, by repeated uses of the loop body, a `Program` fragment representing the
`while` loop may be constructed.

```agda
    -- with some work this could be made tail recursive (thus using O(1) space)
    loop :
      (n : ℕ) →
      Program s ⊤
        (lo ↦ fib zero ∷ hi ↦ fib (suc zero) ∷ [])
        (λ _ → lo ↦ fib n ∷ hi ↦ fib (suc n) ∷ [])
    loop zero    = return tt
    loop (suc n) = do
      loop n
      loopBody n
```

Finally, the definition of `calcFib` can be completed by wrapping the loop in
with appropriate allocations and the `return`.

```agda
  calcFib zero    = return ⦇ zero ⦈
  calcFib (suc n) = do
    lo ← alloc
    write lo zero
    hi ← frame (lo ↦ zero ∷ []) alloc
    frame (lo ↦ zero ∷ []) (write hi (suc zero))
    restructure ([ hi ↦ suc zero ∷ [] ]&[ lo ]⨾[ [] ]⨾⨾ [ [] ]&[ hi ]⨾[ [] ]⨾⨾ ∎)
    FibBody.loop lo hi n
    restructure ([ lo ↦ fib n ∷ [] ]&[ hi ]⨾[ [] ]⨾⨾ ╳)
    ret ← read hi
    restructure ╳
    return ret
```

Compiling Correctly
---
```agda
module CompilingCorrectly where
```

The signature for `Program` and its operations as so far chosen is good enough
for programming, and even for verified programming. (In fact, our design so far
lines up a great deal with the design in [Ynot], except we a. do not support
exceptions, b. require programs to provably terminate successfully with a value,
and c. provide an equivalent to `runST` that can run an imperative program in a
pure context.) However, it has some deficits related to compilation and
execution.

The problem is best encapsulated in the signature of `read`, which is repeated below

```agda
  _ :
    let open AddingSpecifications in
    ∀ {s A} (r : Ref s) {x : A} → Program s (Exactly x) ((r ↦ x) ∷ []) (λ _ → (r ↦ x) ∷ [])
  _ = AddingSpecifications.read
```

Since the value returned by `read` is itself an argument to `read`, a `Program`
that uses `read` not only describes an imperative sequence of instructions, but
necessarily contains pure code that describes all the values used over the
course of the computation. In the Fibonacci example above, every use of `read`
in `calcFib` implicitly refers to the inefficient functional definition `fib`.
The existence of this pure code is not itself a problem, since pure definitions
are required to prove `Program` correctness. The issue is that the pure code
that serves to specify the behavior of an imperative `Program` is itself
executable and compilable. Especially when the functional specification of a
`Program` is slower than the `Program` itself, it is desirable to enforce a
separation between values that are intended only for use in specifications and
that should not be realized in the compiled code and values that are meant to
exist at runtime.

Thus the signature of `Program` is revised with erasure annotations. The erasure
modality `@0` is a feature of Agda's type system that is exactly for tracking
which variables and definitions in an Agda program are meant to be compiled and
which are meant to be erased. Every value that is required only to specify the
behavior of a `Program` is marked as erased. Only values that are truly needed
to execute a `Program` are left in the default modality.

```agda
  postulate
    Ref     : Set → Set
  infix 6 _↦_
  record Assignment (s : Set) : Set₁ where
    constructor _↦_
    field
      var           : Ref s
      {contentType} : Set₀
      content       : contentType
  Condition : Set → Set₁
  Condition s = List (Assignment s)
  -- no changes up to this point

  postulate
    -- erasure is not strictly necessary for arguments of a type constructor
    -- (types usually appear in erased contexts)
    -- but Agda's unifier seems to get confused without these annotations
    Program : (s : Set) (A : Set) → @0 Condition s → @0 (A → Condition s) → Set

    runProgram : ∀ {A}     → ({s : Set} → Program s A [] (λ _ → [])) → A -- no change

    -- the Condition arguments are needed to relate pre- and post-conditions but do not affect execution
    -- note that return values (the argument of return and the value bound by _>>=_) are *not* erased
    return     : ∀ {s A}     {@0 cond : A → Condition s} (x : A) → Program s A (cond x) cond
    _>>=_      : ∀ {s A B}   {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
                 Program s A pre mid →
                 ((x : A) → Program s B (mid x) post) →
                 Program s B pre post

    alloc : ∀ {s} → Program s (Ref s) [] (λ r → (r ↦ tt) ∷ []) -- no change
    -- the old value being overwritten does not affect execution, but the new value certainly does
    write : ∀ {s} {@0 A} {B} (r : Ref s) {@0 x : A} (y : B) → Program s ⊤ ((r ↦ x) ∷ []) (λ _ → (r ↦ y) ∷ [])
```
<!--
```agda
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring {s} : Condition s → Condition s → Set₁ where
    [_]╳ : (discards : Condition s) → Restructuring discards []
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition s)
      (v : Ref s) {A} {x : A}
      (r : Condition s) {rest : Condition s} →
      Restructuring (l ++ r) rest →
      Restructuring (l ++ v ↦ x ∷ r) (v ↦ x ∷ rest)
  postulate
```
-->
```agda
    -- definition of Restructuring again omitted
    -- not only do Conditions not matter for execution, Restructurings don't either
    restructure : ∀ {s} {@0 pre post : Condition s} → @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
    frame :
      ∀ {s A} (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
      Program s A pre post → Program s A (pre ++ side) (λ x → post x ++ side)
```

Again, in order to give `read` a type, an auxiliary data type is needed to
relate the value returned to the value predicted. This type is similar to
`Exactly`, except it asserts the equality of the contained value to an *erased*
specification.

```agda
  data Realizer {A : Set} : @0 A → Set where
    realized : (x : A) → Realizer x
  postulate
    -- given a "hypothetical" value x, when that value is behind r, `read r` returns a real value equal to x
    read : ∀ {s A} (r : Ref s) {@0 x : A} → Program s (Realizer x) ((r ↦ x) ∷ []) (λ _ → (r ↦ x) ∷ [])
```

The inefficient functional version of `fib` can be marked as erased:

```agda
  @0 fib : ℕ → ℕ
  fib zero          = zero
  fib (suc zero)    = suc zero
  fib (suc (suc n)) = fib n + fib (suc n)
```

But it can still be used to specify the behavior of `calcFib`, which can now be
guaranteed to never call the inefficient definition at runtime.

```agda
  calcFib : ∀ {s} (n : ℕ) → Program s (Realizer (fib n)) [] (λ _ → [])
  calcFib = {! complete example in FibonacciManual, see below !}
```

Transfinite Universes
---
Through this point, all the values `x : A` being stored in `Ref`s have had types
`A : Set`. Unlike Haskell, Agda does not have just one "type of types" (which in
Haskell is called `Type` and satisfies `Type :: Type`). Such a situation leads
to paradoxes. Instead, Agda has an infinite hierarchy of universes
`Set = Set₀ : Set₁ : ...`. While most simple data types belong to `Set₀` (for
example, `ℕ : Set₀`), it might be desirable to data in larger universes to be
stored in mutable cells. However, there is a subtle problem with just allowing
data of any type to appear in `Program`s.

The potential problem comes from the following operations, where the types have
once again been revised to allow freedom of universe levels.

```agda
module UniverseProblem where
  postulate
    Ref     : Set → Set -- Refs continue to live in the lowest universe
  infix 1 _↦_
  record Assignment (s : Set) : Setω₀ where -- Setω₀ is a transfinite universe above all the finite Setᵢs
    constructor _↦_
    field
      var            : Ref s
      {contentLevel} : Level -- Assignments need to be able to describe variable contents at any level
      {contentType}  : Set contentLevel
      content        : contentType
  infixr 0 _⨾_
  data Condition (s : Set) : Setω₀ where -- Condition can no longer be defined in terms of List
    𝟏   : Condition s
    _⨾_ : Assignment s → Condition s → Condition s
  postulate
    Program : ∀ {ℓ} (s : Set) (A : Set ℓ) → @0 Condition s → @0 (A → Condition s) → Set ℓ

    runProgram : ∀ {ℓ} {A : Set ℓ} → ({s : Set} → Program s A 𝟏 (λ _ → 𝟏)) → A
    alloc : ∀ {s} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
    -- revised types for return, _>>=_ and restructure omitted
```
<!--
```agda
    return : ∀ {s ℓ} {A : Set ℓ} {@0 cond : A → Condition s} (x : A) → Program s A (cond x) cond
    _>>=_ :
      ∀ {s ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
  _>>_ :
      ∀ {s ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ({x : A} → Program s B (mid x) post) → Program s B pre post
  p >> q = do
    x ← p
    q {x}

  infixr 0 _&_
  _&_ : ∀ {s} → Condition s → Condition s → Condition s
  𝟏           & r = r
  (v ↦ x ⨾ l) & r = v ↦ x ⨾ l & r
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring {s} : Condition s → Condition s → Setω₀ where
    [_]╳ : (discards : Condition s) → Restructuring discards 𝟏
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition s)
      (v : Ref s) {ℓ} {A : Set ℓ} {x : A}
      (r : Condition s) {rest : Condition s} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
  pattern ╳ = [ _ ]╳
  postulate
    restructure : ∀ {s} {@0 pre post : Condition s} → @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
```
-->

The issue is that it is now possible to smuggle a `Ref` through `runProgram` by
pairing it with the state thread provided by `runProgram`.

```agda
  record ARef : Set₁ where
    constructor aRef
    field
      {stateThread} : Set
      ref : Ref stateThread
  x : ARef
  x = runProgram do
    r ← alloc
    restructure ╳
    return (aRef r)
  y : ARef
  y = runProgram do
    r ← alloc
    restructure ╳
    return (aRef r)
```

Since `x` and `y` have syntactically equal definitions, Agda proves that they
are equal.

```agda
  _ : x ≡ y
  _ = refl
```

However, it is not necessarily the case that `x` and `y` actually evaluate to
the same value, since they could be the results of two different `runProgram`s
which do their own `alloc`s. (Or, the implementation could detect possible
sharing between `x` and `y` and actually make them equal. The point is that the
equality of `x` and `y` is unspecified.)

The problem can be fixed by stopping state threads from being returned by
`runProgram`. Previously, this was ensured by using `Set₀ : Set₁` as the type of
state threads while only allowing `runProgram` to return values `x : A : Set₀`,
and in general smuggling state threads is correctly prohibited if the type of
state threads belongs to a universe strictly larger than any universe that can
be used in `runProgram`. In order to preserve the polymorphism of `runProgram`
over all finite universes `Set ℓ`, the type of state threads needs to belong to
`Setω₀` or higher. We choose to postulate an abstract type of state threads in
`Setω₀`. (Note that Haskell's choice to use `Type` as the type of state threads
is historical. A state thread does not actually need to be a type.)

```agda
module TransfiniteUniverses where
  postulate
    StateThread : Setω₀
    Ref         : StateThread → Set
  infix 1 _↦_
  record Assignment (s : StateThread) : Setω₀ where
    constructor _↦_
    field
      var            : Ref s
      {contentLevel} : Level
      {contentType}  : Set contentLevel
      content        : contentType
  infixr 0 _⨾_
  data Condition (s : StateThread) : Setω₀ where
    𝟏   : Condition s
    _⨾_ : Assignment s → Condition s → Condition s
  postulate
    Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) → Condition s → (A → Condition s) → Set ℓ
    -- remainder of signature omitted for brevity
```

Arrays
---
So far, the memory accessible to imperative programs has been modeled as
consisting of simply disparate cells. However, a key advantage of imperative
languages over pure functional languages is the ability to access memory via
arrays. Ignoring the hierarchical structure of modern memory, an imperative
program can read or write an element in an array by its index in `O(1)` time.
Pure functional code can efficiently read from arrays, but updates may have to
copy the entire array. For some algorithms, it may be possible to batch updates
such that the overhead of copying is acceptable, but in general an imperative
model is most appropriate for array-based programming. Alternatively, there
exist pure functional tree-based data structures that allow storing sequences of
elements with `O(log n)` reads and updates (waving hands, this is asymptotically
the same as imperative access to hierarchical memory), but absolute performance
still suffers due to the cost of indirection.

Haskell code in `ST` can partake in the performance benefits of true mutable
arrays by using `STArray` instead of `STRef`. One possible way to model these
arrays in the context of `Program` is to simply define an array as a function
from indices to `Ref`s, and have a `Program` operation that creates such a
function.

```agda
module Arrays? where
  open TransfiniteUniverses

  Array : StateThread → @0 ℕ → Set
  Array s n = (i : ℕ) → @0 .(i < n) → Ref s
```

However, such a representation runs into technical issues in that unifying
expressions of type `Array` becomes difficult. Producing subarrays from arrays
is also problematic, as such an operation must precompose the
array-as-a-function with the addition of an offset, so repeatedly forming
subarrays produces an `Array` of `O(n)` size and that takes `O(n)` time to
index.

Instead, we introduce `Array` as a primitive type, replacing `Ref`. An `Array n`
represents a *contiguous* block of `n` memory cells.

```agda
module Arrays where
  postulate
    StateThread : Setω₀
    Array       : StateThread → @0 ℕ → Set
```

Instead of being an abstract type, `Ref` can be concretely defined as a record
type consisting of a base `Array` and an index.

```agda
  module BasicConcreteRef where
    record Ref (s : StateThread) : Set where
      field
        @0 {underlyingLength} : ℕ
        underlying : Array s underlyingLength
        index : ℕ
        @0 .indexValid : index < underlyingLength
```

Since `Array` is an abstract type, expressions of type `Array` will usually be
variables and thus easy to unify. Further, arithmetic operations on `Ref`s incur
their cost once instead of at every use. In fact, `Ref` can be slightly
generalized to `Slice` to represent references to whole contiguous ranges of
cells inside `Array`s:

```agda
  record Slice (s : StateThread) (@0 n : ℕ) : Set where
    constructor slice
    field
      @0 {underlyingLength} : ℕ
      underlying : Array s underlyingLength
      offset : ℕ
      @0 .fit : offset + n ≤ underlyingLength
  Ref : StateThread → Set
  Ref s = Slice s 1
```

The operation `alloc`, which previously created a single `Ref`, can now be
replaced with an operation `allocArray` that allocates a whole array. The
original signature of `alloc` can be implemented in terms of `allocArray` as a
convenience. The rest of the operations, which refer to `Ref`s, can stay as they
are.

Final Interface
---
We package the finalized signature of all the types and operations needed for
imperative programming in `Program` into the following Agda record type:

```agda
import Imperative
_ : Setω₁
_ = Imperative.Impl
```

By using a record type instead of bare `postulate`s, it is possible to present
multiple implementations of the same signature and to write `Program` programs
in `--safe` files (which cannot use `postulate`s) by generalizing over an
`Imperative.Impl` parameter.

Implementation
===
It remains to provide an implementation of `Program` and its associated
operations. We actually do this twice. The "intended" implementation,
`Imperative.ST` unsafely imports Haskell's `ST` interface into Agda and then
implements the hopefully-safe signature in terms of the basic operations.

```agda
open import Imperative.ST
_ : Imperative.Impl
_ = ST
```

In order to remove the possibility that the basic types and operations, taken
together, are somehow incompatible (i.e. are inconsistent, lead to a
contradiction), a second implementation in pure, safe Agda that "simulates"
every imperative operation with no care for efficiency is also provided. Because
the pure implementation exists, it is assured that the design of `Program` is
not so fundamentally flawed as to break or change the logical strength of Agda
as a theorem prover. The correctness of the compilation of the basic operations
to Haskell is not as easily verified. It is, however, relatively simple,
minimizing the amount of unsafe code that must be trusted.

```agda
open import Imperative.Pure
@0 _ : Imperative.Impl
_ = Pure
```

A helper module reexporting everything that is needed to write `Program`s is
also provided. A complete example of using `Program` to compute Fibonacci
numbers is provided.

```agda
import Imperative.ManualStyle
import FibonacciManual
```

Manually specifying all uses of `restructure` and `frame` is tedious and
introduces an excess of proof noise into even simple algorithms. Therefore,
automation via Agda's reflection facilities is also provided to suppress the
most trivial uses of these functions. The Fibonacci example is repeated in the
new syntax, and a further example of a correct-by-construction insertion sort on
an array of `ℕ`s is also given.

```agda
import Imperative.AutomaticStyle
import Fibonacci
import InsertionSort
```

In any case, since `Program`s are delimited by `runProgram`, they can, once
defined, appear in arbitrary Agda code. For example, all of the above programs
can be compiled into an executable that, at the top level, looks like perfectly
ordinary Agda.

```agda
import Main
```
