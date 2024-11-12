In this file, we collect the definitions of the auxiliary data types used in the
definition of `Imperative.Impl` from the files in which they are defined, and
specialize their parameters in terms of the fields of `Imperative.Impl`. First,
the top-level module of the file is declared as parameterized over the relevant
fields.

```
{-# OPTIONS --safe #-}
```

<!--
```
open import Agda.Primitive
open import Data.Nat
```
-->

```
module Imperative.Specifications (StateThread : Setω₀) (Array : StateThread → @0 ℕ → Set lzero) where
```

<!--
```
import Imperative.Slice
import Imperative.Condition
```
-->

The first data types we need are `Slice` and `Ref`, which represent the memory
references manipulated by imperative programs. We import them in their general,
parameterized form...

```
open Imperative.Slice renaming (Slice to GenSlice; Ref to GenRef)
```

...and specialize them as needed.

```
Slice : StateThread → @0 ℕ → Set lzero
Slice s = GenSlice (Array s)
Ref : StateThread → Set lzero
Ref s = GenRef (Array s)
```

We also need `Condition`, which is a data type for describing states of the
heap. Again, we take it from its defining module...

```
open Imperative.Condition renaming (Condition to GenCondition)
```

...and specialize it.

```
Condition : StateThread → Setω₀
Condition s = GenCondition (Ref s)
```
