Here we declare the primitive data and operations needed to embed and run
provably correct imperative programs inside a dependently typed pure functional
language. Note that this module is `--safe` because it does not attempt to
define an implementation of the specified primitives. Imperative programs are
meant to be written by generalizing over an `Imperative.Impl` argument, which is
a record type whose fields hold the primitives. Unsafety is required only at the
top level to pass the efficient implementation `Imperative.ST` in.

```
{-# OPTIONS --safe #-}
module Imperative where
```

<!--
```
open import Agda.Primitive
open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality

open import ArrayValue
open import Erased
open import Realizer

open import Imperative.Slice hiding (Slice; Ref)
open import Imperative.Condition hiding (Condition)
import Imperative.Specifications
import Imperative.Restructuring
import Imperative.Framing
```
-->

```
record Impl : Setω₁ where
  field
```

The first required primitive is a type of "state threads". These threads may be
thought of as tokens that identify what state the other operations should
access. Note that this type lives in a very large universe: this is necessary to
make sure the token cannot escape through the return value of a program. (That
is, a `StateThread` cannot "fit through" `runProgram` as declared below.) This
would be bad, since then it would also be possible to have mutable references
escape the program. Since two evaluations of a program that allocates memory can
get different references, letting the state thread escape actually breaks
referential transparency. In the implementation, the state thread represents the
phantom type parameter that Haskell's `Control.Monad.ST` uses to ensure purity.

```
    StateThread : Setω₀
```

The next required primitive is a type of allocations. Each value of this type
represents a region of memory which can be accessed from a certain state thread
and which has enough space to store a certain number of values (of any type in a
`Set` universe). Note that the "length" parameter is marked as erased: it is not
strictly required to know the length of an allocation at runtime to use it. (The
type checker will strictly enforce that all accesses are correct!) Note that
this type lives in a small universe, so it acts like "just another Agda type"
that can appear in `List`s, etc.

```
    Array : StateThread → @0 ℕ → Set lzero
```

Note that an Agda `record` not only defines a record type with fields, but can
also export other definitions. The following line exports certain parameterized
types needed to represent memory references and heap states specialized to this
`Imperative.Impl`. Specifically we specialize the named module by applying it to
the fields above, and then bring its contents into scope and reexport them. (It
is suggested to read through the linked definitions before continuing in this
file.)

```
  open Imperative.Specifications StateThread Array public
```

Having defined ways to refer to and specify the contents of memory, we now
continue declaring primitive operations. The first of these is `Program`, which
forms the types of imperative programs. A `Program s A pre post` is a sequence
of instructions that can run in the state thread `s : StateThread` on top of a
heap initially described by `pre : Condition s` (the *precondition*), and
finishes by returning a value `x : A` while leaving the heap in a state
described by `post x : Condition s` (the *postcondition*). Note that the state
of the heap after the program has run may depend on the returned value.

```
  field
    Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) (@0 pre : Condition s) (@0 post : A → Condition s) → Set ℓ
```

The return value of a program that has an empty precondition and can run on an
arbitrary state thread is a pure function of the program. Such a program cannot
read any mutable variables that it does not allocate itself and cannot return
any references (which can be different between runs) to the allocations it
makes. `runProgram` gives the pure function from such programs to values. (The
type of `runProgram` requires the postcondition of the program to also be empty.
This helps type inference and there should not be any way to write a nontrivial
term of type `Condition s` in the required position anyway.)

```
    runProgram :
      ∀ {ℓ} {A : Set ℓ} →
      ({s : StateThread} → Program s A 𝟏 (λ _ → 𝟏)) → A
```

A simple program `return x : Program s A (cond x) cond` exists for each value
`x : A`. This program touches no state and just returns the value `x`. Note that
the heap state gets generalized over `x`: though the actual state at runtime
need not change when a `return` executes, the compile-time description of the
state changes to "forget" the value of `x`. Also note that the argument `cond`
describing the state of the heap is erased (programs do not have to waste time
and space tracking what is on the heap).

```
    return :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 cond : A → Condition s}
      (x : A) → Program s A (cond x) cond
```

Smaller programs can be combined with a monad-like `_>>=_` operator. `p >>= q`
is a program that first runs `p : Program s A pre mid` on the state `pre` to get
a value `x : A` while changing the state to `mid x`. Then a new program
`q x : Program s B (mid x) post`, perhaps depending on `x`, is computed and then
run (note that the postcondition of `p` and the precondition of `q` are required
to match) to arrive at a value `y : B` in a state `post y`.

Agda expands Haskell-like `do` notation in terms of `_>>=_`:
`do { pat ← stmt; stmts...}` becomes `stmt >>= λ pat → do { stmts... }`. Agda
differs from Haskell in that the `_>>=_` in the above expansion is not a
specific defined entity but rather whatever the name `_>>=_` currently refers
to. Thus, when this function is in scope, `do` notation is supported for
`Program`, even though `Program` is not declared as any kind of monad.

```
    _>>=_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
```

For any memory reference `r` live in a `StateThread` `s`, `read r` is a
`Program` that returns the value behind `r` and does nothing to the program
state. Note that `read` takes an argument `@0 x : A` representing the value that
is going to be read! This does not defeat the purpose of writing the imperative
program because the argument `x` will not be compiled and evaluated at runtime.
Rather, the argument `@0 x : A` enforces only that we *logically* know (that is,
have an expression at compile-time for) the value behind `r`. The presence of
such an argument is required even to state the pre- and post-conditions of
`read r`. Also note that the type of the return value of `read` is not just `A`,
but the more specific `Realizer x`. A `Realizer x` wraps a *non-erased* (present
at runtime) value of type `A` that is forced to be equal to `x`. The idea is
that sometimes there may be an imperative program that produces a `Realizer x`
faster than the functional expression `x` can be evaluated. (For example,
`read`ing a reference that is known to contain `lookup xs i` can produce a
`Realizer` for `lookup xs i` much faster than `lookup xs i` can evaluate.)

```
    read :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
      (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
```

Conversely, given a memory reference `r` and a value `y : B`, the program
`write r y` changes a heap satisfying the precondition `r ↦ x ⨾ 𝟏` (for any
`x : A`) to a heap satisfying `r ↦ y ⨾ 𝟏` (while returning the uninformative
value `tt : ⊤`). Note that `r` must appear in the precondition of `write r y` to
follow the tenets of separation logic: after `write r y`, we not only know that
`r` points to `y`, but we must also destroy our old knowledge that `r` pointed
to `x`. (Note that the level and type of the erased value in `read` are not
erased, but they are erased for `write`. It's possible that the level and type
in `read` could also be made erased, but the current formulation has the
intuitive justification that you need to know, at runtime, the type of a value
in order to safely read it from memory.)

```
    write :
      ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
```

A program may use `allocArray` to allocate a block of contiguous (that is, a
collection that can be indexed) memory cells. The cells are initialized to a
reasonable dummy value (here `tt : ⊤`). `Slice`s, including `Ref`s, can be
derived from the resulting `Array`.

```
    allocArray :
      {s : StateThread} (n : ℕ) →
      Program s (Array s n) 𝟏 (λ r → fullSlice r ↦＊ ArrayValue.replicate n tt)
```

Given a program `p : Program s A pre post`, it is possible to run `p` on any
heap that contains a subpart described by `pre` (without requiring that `pre`
describe the whole heap). Such a heap generically satisfies the condition
`pre & side` for some `side`. Running `p` is guaranteed not to change the parts
of the heap described by `side`, hence the state afterwards is `post x & side`,
where `x` is the return value of `p`. This principle is traditionally called the
*frame rule* and allows building imperative programs compositionally. The
program `p` adapted to run in a heap with an extra part described by `side` is
`frame side p`.

```
    frame :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ}
      (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
      Program s A pre post → Program s A (pre & side) (λ x → post x & side)
```

Like as seen in `return`, certain changes to the heap description can occur
without actually performing any action. For example, taking the precondition
`x ↦ 1 ⨾ y ↦ 2 ⨾ 𝟏` to the postcondition `y ↦ 2 ⨾ x ↦ 1 ⨾ 𝟏` or even the
postcondition `x ↦ 1 ⨾ 𝟏` requires no action at all. The program `restructure p`
is a program that performs no action but can still have differing pre- and
post-conditions as long as `p` gives a proof that they are related by simple
reordering and discarding (essentially, by *structural rules*). The type of such
proofs is called `Restructuring` and lives in yet another module.

```
  open Imperative.Restructuring
  field
    restructure :
      {s : StateThread} {@0 pre post : Condition s} →
      @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
```

The following operation reflects the central tenet of separation logic into a
proof value usable by the program: running the program `separate` on any heap
state produces a proof that all the live heap locations are distinct from each
other. It is not used too often but is still here for completeness.

```
    separate : {s : StateThread} {@0 cond : Condition s} → Program s (Erased (Unique (liveRefs cond))) cond (λ _ → cond)
```

This concludes the primitive types and operations. We now take the liberty of
putting some basic utilities into the record module as well. (The following
definitions are not fields of the record, but are still members of the record
module and come into scope when the record is opened.)

When Agda desugars a `do`-statement that does *not* bind its return value, it
uses the operation `_>>_` instead of `_>>=_`: `do { stmt; stmts... }` becomes
`stmt >> do { stmts... }`. Thus we need to define `_>>_` in order to get
reasonable `do`-notation for `Program`. Since the heap state after the
discarded-value statement might still depend on the value returned, the solution
taken here is to make `_>>_` identical to `_>>=_` but have the "discarded" value
enter the continuation as an *implicit* argument. A different choice would be to
require that the heap state after a discarded-value statement not depend on the
returned value, in which case that value is not forced to be available.

```
  _>>_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ({x : A} → Program s B (mid x) post) → Program s B pre post
  p >> q = do
    x ← p
    q {x}
```

Whereas `write r y` writes an unwrapped value `y` to `r`, `writeRealized r y′`
requires `y′ : Realizer y` to be a value equivalent to `y` wrapped up as a
`Realizer`. Note that `writeRealized r y′` is distinct from
`write r (realized y′)`, which has postcondition `r ↦ realized y′ ⨾ 𝟏` instead
of `r ↦ y ⨾ 𝟏`. The difference is exactly rewriting by `realizes y′`.

```
  writeRealized :
    ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A} {@0 y : B}
    (r : Ref s) → Realizer y → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
  writeRealized r (realized y) = write r y
```

It is possible to allocate a single memory cell by just allocating an array of
size `1`. As this is perhaps the first nontrivial program written in `Program`,
for explanatory purposes the type of each line and the expected type after each
line (that is, the type of the hole left if the remainder of the `do` block is
deleted and replaced with a `?`) is shown. Note that this information is just
what Agda's interactive mode supplies when an interaction point is placed in a
`Program` `do`-block.

```
  alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
  alloc = do
    -- the rest of the block should be a Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
    a ← allocArray 1 -- allocArray 1 : Program s (Array s 1) 𝟏 (λ r → fullSlice r ↦ tt ⨾ 𝟏)
    -- with a : Array s 𝟏 in the context, a Program s (Ref s) (fullSlice a ↦ tt ⨾ 𝟏) (λ r → r ↦ tt ⨾ 𝟏) is wanted
    return (fullSlice a)
      -- return {cond = λ r → r ↦ tt ⨾ 𝟏} (fullSlice a) : Program s (Ref s) (fullSlice a ↦ tt) (λ r → r ↦ tt ⨾ 𝟏)
```

It is also possible to allocate a memory location and initialize it with a given
value.

```
  init : ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
  init {x = x} xᵣ = do
    -- wanted: Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
    v ← alloc -- given: Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
    -- given v : Ref s, wanted: Program s (Ref s) (v ↦ tt ⨾ 𝟏) (λ r → r ↦ x ⨾ 𝟏)
    writeRealized v xᵣ -- given: Program s ⊤ (v ↦ tt ⨾ 𝟏) (λ _ → v ↦ x ⨾ 𝟏)
    -- wanted: Program s (Ref s) (v ↦ x ⨾ 𝟏) (λ r → r ↦ x ⨾ 𝟏)
    return v -- inferring {cond = λ r → r ↦ x ⨾ 𝟏}, given: Program s (Ref s) (v ↦ x ⨾ 𝟏) (λ r → r ↦ x ⨾ 𝟏)
```

Finally, we can read and write whole `Slice`s by using `read` and `write`
repeatedly. Note that writing values of heterogenous types is easy in
`writeSlice` as we have the type `ArrayValue`, but reading values of
heterogenous types is not as easy since we'd need a non-erased witness of those
types. Instead we only have a homogeneous read operation `readVec`.

Note that many explicit uses `frame` and `restructure` are required to glue the
changes to the heap state together. `Imperative.Framing` is used to write the
`Restructuring` proof terms more conveniently.

```
  open Imperative.Framing
  writeSlice :
    {s : StateThread} {@0 n : ℕ} {@0 pre : ArrayValue n} (arr : Slice s n) (xs : ArrayValue n) →
    Program s ⊤ (arr ↦＊ pre) (λ _ → arr ↦＊ xs)
  writeSlice {pre = []}      arr []       = return tt -- inferring {cond = λ _ → 𝟏}, wanted/given: Program s ⊤ 𝟏 𝟏
  writeSlice {pre = p ∷ pre} arr (x ∷ xs) = do
    -- wanted: Program s ⊤ (* arr ↦ p ⨾ ++ arr ↦＊ pre) (λ _ → * arr ↦ x ⨾ ++ arr ↦＊ xs)
    frame (++ arr ↦＊ _) (write (* arr) x)
      -- under frame, given: Program s ⊤ (* arr ↦ p ⨾ 𝟏) (λ _ → * arr ↦ x ⨾ 𝟏)
      -- framed, have:       Program s ⊤ (* arr ↦ p ⨾ ++ arr ↦＊ pre) (λ _ → * arr ↦ x ⨾ ++ arr ↦＊ pre)
    -- wanted: Program s ⊤ (* arr ↦ x ⨾ ++ arr ↦＊ pre) (λ _ → * arr ↦ x ⨾ ++ arr ↦＊ xs)
    restructure (unfocus (((* arr ⨾⨾ 𝟏) &> >[ ++ arr ↦＊ _ ]<) <&> >[ * arr ⨾⨾ 𝟏 ]<))
      -- read the argument to unfocus as:
      --   first, write the precondition as (* arr ⨾⨾ 𝟏) & (++ arr ↦＊ _). take the right part.
      --   then, what is left over is (* arr ⨾⨾ 𝟏). take that too.
      --   and produce the postcondition by _&_ing these
      -- thus, have: Program s ⊤ (* arr ↦ x ⨾ ++ arr ↦＊ pre) (λ _ → ++ arr ↦＊ pre & * arr ↦ x ⨾ 𝟏)
    -- wanted: Program s ⊤ (++ arr ↦＊ pre & * arr ↦ x ⨾ 𝟏) (λ _ → * arr ↦ x ⨾ ++ arr ↦＊ xs)
    frame (* arr ⨾⨾ 𝟏) (writeSlice (++ arr) xs)
      -- under frame, given: Program s ⊤ (++ arr ↦＊ pre) (λ _ → ++ arr ↦＊ xs)
      -- thus have: Program s ⊤ (++ arr ↦＊ pre & * arr ↦ x ⨾ 𝟏) (λ _ → ++ arr ↦＊ xs & * arr ↦ x ⨾ 𝟏)
    -- wanted: Program s ⊤ (++ arr ↦＊ xs & * arr ↦ x ⨾ 𝟏) (λ _ → * arr ↦ x ⨾ ++ arr ↦＊ xs)
    restructure (unfocus (((++ arr ↦＊ _) &> >[ * arr ⨾⨾ 𝟏 ]<) <&> (>[ ++ arr ↦＊ _ ]< <& 𝟏)))
      -- read the argument to unfocus as:
      --   first, write the precondition as (++ arr ↦＊ _) & (* arr ⨾⨾ 𝟏). take the right part.
      --   then, what is left over is (++ arr ↦＊ _) & 1. take the left part.
      --   and produce the postcondition by _&_ing these
      -- thus, have: Program s ⊤ (++ arr ↦＊ xs & * arr → x ⨾ 𝟏) (λ _ → * arr → x ⨾ ++ arr ↦＊ xs)

  -- hopefully the following also makes sense now
  readVec :
    ∀ {s : StateThread} {ℓ} {A : Set ℓ} {n : ℕ} (arr : Slice s n) {@0 xs : Vec A n} →
    Program s (Realizer xs) (arr ↦＊ vec xs) (λ _ → arr ↦＊ vec xs)
  readVec {n = zero}  arr {xs = []}     = return (realized [])
  readVec {n = suc n} arr {xs = x ∷ xs} = do
    realized .x ← frame (++ arr ↦＊ _) (read (* arr))
    restructure (unfocus (((* arr ⨾⨾ 𝟏) &> >[ ++ arr ↦＊ _ ]<) <&> >[ * arr ⨾⨾ 𝟏 ]<))
    realized .xs ← frame (* arr ⨾⨾ 𝟏) (readVec (++ arr))
    restructure (unfocus (((++ arr ↦＊ _) &> >[ * arr ⨾⨾ 𝟏 ]<) <&> (>[ ++ arr ↦＊ _ ]< <& 𝟏)))
    return (realized (x ∷ xs))
```

Suggested reading after this file is `Imperative.Pure` and `Imperative.ST` to
see two different implementations of `Imperative.Impl` and `Imperative.Solvers`
to see how applications of `frame` and `restructure` may be automated.
