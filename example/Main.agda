{-# OPTIONS --guardedness #-}
module Main where

open import Agda.Builtin.String
import Data.Nat.Show as ℕ
open import Data.Maybe using (Maybe)
open Maybe
open import Function.Base
open import IO

open import Fibonacci
open import Imperative.ST

main : Main
main = run do
  n ← ℕ.readMaybe 10 <$> getLine
  case n of λ where
    nothing  → putStrLn "invalid index"
    (just n) → putStrLn (primShowNat (fib′ ST n))
