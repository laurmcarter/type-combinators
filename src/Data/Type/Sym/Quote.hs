{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Sym.Quote
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A 'QuasiQuoter' for the 'Sym' type.
--
-- The 'ix' quasiquoter can be used in either expression or pattern contexts.
-- It accepts integers, starting at 0, for @IZ@, @(IS IZ)@, and so on,
-- as well as expressions of the form '<var> + <int>'.
-- This latter form binds the variable or lifts the variable inside
-- the appropriate number of @IS@ constructors in pattern and expression contexts,
-- respectively.
--
-- e.g.
--
--     >>> [ix|x+2|] ==> IS (IS x)
--
-----------------------------------------------------------------------------

module Data.Type.Sym.Quote
  ( sym
  ) where

import Data.Type.Sym
import Language.Haskell.TH
import Language.Haskell.TH.Quote

sym :: QuasiQuoter
sym = QuasiQuoter
  { quoteExp  = parseSymExp
  , quotePat  = error "sym: quotePat not defined"
  , quoteType = parseSymType
  , quoteDec  = error "sym: quoteDec not defined"
  }

parseSymExp :: String -> Q Exp
parseSymExp s = [| Sym :: $(parseSymType s) |]

parseSymType :: String -> Q Type
parseSymType s = [t| Sym $(litT $ strTyLit s) |]

