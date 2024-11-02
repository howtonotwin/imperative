{-# OPTIONS --guardedness #-}
module Main where

open import Agda.Primitive
open import Agda.Builtin.String
open import Data.Nat
import Data.Nat.Show as ℕ
open import Data.List
open import Data.Maybe using (nothing; just)
open import Data.Product
open import Data.Unit.Polymorphic
import Data.Vec as Vec
open import Function
open import IO
open import System.Environment

import Fibonacci
import FibonacciManual
import InsertionSort
open import Imperative.ST

{-# NON_TERMINATING #-}
readList : IO (List ℕ)
readList = do
  n ← ℕ.readMaybe 10 <$> getLine
  case n of λ where
    nothing  → pure []
    (just n) → (n ∷_) <$> readList
writeList : List ℕ → IO {lzero} ⊤
writeList []       = pure tt
writeList (n ∷ ns) = do
  putStrLn (primShowNat n)
  writeList ns

mains : List String → IO ⊤
mains ("fib"           ∷ []) = do
  n ← ℕ.readMaybe 10 <$> getLine
  case n of λ where
    nothing  → putStrLn "invalid index"
    (just n) → putStrLn (primShowNat (Fibonacci.fib′ ST n))
mains ("fibManual"     ∷ []) = do
  n ← ℕ.readMaybe 10 <$> getLine
  case n of λ where
    nothing  → putStrLn "invalid index"
    (just n) → putStrLn (primShowNat (FibonacciManual.fib′ ST n))
mains ("insertionSort" ∷ []) = do
  ns ← readList
  let ns′ , _ = InsertionSort.sorted ST (Vec.fromList ns)
  writeList (Vec.toList ns′)
mains _                      = putStrLn "don't understand arguments"

main : Main
main = run (getArgs >>= mains)
