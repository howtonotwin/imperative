{-# OPTIONS --guardedness #-}
module Main where

open import Agda.Builtin.String
import Data.Nat.Show as ℕ
open import Data.List
open import Data.Maybe using (nothing; just)
open import Data.Unit.Polymorphic
open import Function
open import IO
open import System.Environment

import Fibonacci
import FibonacciManual
open import Imperative.ST

mains : List String → IO ⊤
mains ("fib"       ∷ []) = do
  n ← ℕ.readMaybe 10 <$> getLine
  case n of λ where
    nothing  → putStrLn "invalid index"
    (just n) → putStrLn (primShowNat (Fibonacci.fib′ ST n))
mains ("fibManual" ∷ []) = do
  n ← ℕ.readMaybe 10 <$> getLine
  case n of λ where
    nothing  → putStrLn "invalid index"
    (just n) → putStrLn (primShowNat (FibonacciManual.fib′ ST n))
mains _                  = putStrLn "don't understand arguments"

main : Main
main = run (getArgs >>= mains)
