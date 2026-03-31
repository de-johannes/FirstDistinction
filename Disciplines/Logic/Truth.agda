{-# OPTIONS --safe --without-K #-}

module Disciplines.Logic.Truth where

-- Minimal truth type, kept local to Disciplines so we do not import unrelated modules.

data ⊤ : Set where
  tt : ⊤
