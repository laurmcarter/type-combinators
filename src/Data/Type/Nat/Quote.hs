{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Index.Quote
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A 'QuasiQuoter' for the 'N' kind and the 'Nat' type.
--
-- The expression and pattern quasiquoters can accept a variable lifting/binding
-- form, respectively. See Data.Type.Nat.Quote for more details.
--
-----------------------------------------------------------------------------

module Data.Type.Nat.Quote
  ( n , ns
  ) where

import Data.Type.Product
import Data.Type.Nat
import Type.Family.List
import Type.Family.Nat
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Control.Monad
import Text.Read
import GHC.Read (list)
import Data.Maybe (maybeToList)

-- Single N QQ {{{

n :: QuasiQuoter
n = QuasiQuoter
  { quoteExp  = parseE qq >=> eExp
  , quotePat  = parseE qq >=> ePat
  , quoteType = parseE qq >=> eType
  , quoteDec  = stub   qq "quoteDec"
  }
  where
  qq = "n"

-- }}}

-- Multiple Ns QQ {{{

ns :: QuasiQuoter
ns = QuasiQuoter
  { quoteExp  = parseEList qq >=> eListExp
  , quotePat  = parseEList qq >=> eListPat
  , quoteType = parseEList qq >=> eListType
  , quoteDec  = stub       qq "quoteDec"
  }
  where
  qq = "ns"

-- }}}

-- Common Parsing Structure {{{

data NatExp
  = I Int
  | A String Int
  deriving (Eq,Ord,Show)

instance Read NatExp where
  readsPrec d = readParen (d > 10) $ \s0 ->
    [ (A x i,s3)
    | (x,s1)    <- lex s0
    , ("+",s2) <- lex s1
    , (y,s3)   <- lex s2
    , i <- maybeToList $ readMaybe y
    ] ++
    [ (I i,s1)
    | (x,s1) <- lex s0
    , i <- maybeToList $ readMaybe x
    ]
  readList s = readPrec_to_S (list readPrec) 0 $ "[" ++ s ++ "]"

parseEList :: String -> String -> Q [NatExp]
parseEList qq s = case readMaybe s of
  Just es -> allNotNeg qq es
  _       -> fail $ qq ++ ": couldn't parse nat sequence: " ++ show s

parseE :: String -> String -> Q NatExp
parseE qq s = case readMaybe s of
  Just e -> notNeg qq e
  _      -> fail $ qq ++ ": couldn't parse nat expression: " ++ show s

notNeg :: String -> NatExp -> Q NatExp
notNeg qq e = case e of
  I x   | x < 0 -> fail $ qq ++ ": negative: " ++ show x
        | True  -> return e
  A _ x | x < 0 -> fail $ qq ++ ": negative: " ++ show x
        | True  -> return e

allNotNeg :: String -> [NatExp] -> Q [NatExp]
allNotNeg = mapM . notNeg

eExp :: NatExp -> Q Exp
eExp = \case
  I 0   -> [| Z_ |]
  I x   -> [| S_ $(eExp $ I $ x-1) |]
  A x 0 -> varE $ mkName x
  A x y -> [| S_ $(eExp $ A x $ y-1) |]

eListExp :: [NatExp] -> Q Exp
eListExp = \case
  []     -> [| Ø |]
  e : es -> [| $(eExp e) :< $(eListExp es) |]

ePat :: NatExp -> Q Pat
ePat = \case
  I 0   -> [p| Z_ |]
  I x   -> [p| S_ $(ePat $ I $ x-1) |]
  A x 0 -> varP $ mkName x
  A x y -> [p| S_ $(ePat $ A x $ y-1) |]

eListPat :: [NatExp] -> Q Pat
eListPat = \case
  []     -> [p| Ø |]
  e : es -> [p| $(ePat e) :< $(eListPat es) |]

eType :: NatExp -> Q Type
eType = \case
  I 0   -> [t| Z |]
  I x   -> [t| S $(eType $ I $ x-1) |]
  A x 0 -> varT $ mkName x
  A x y -> [t| S $(eType $ A x $ y-1) |]

eListType :: [NatExp] -> Q Type
eListType = \case
  []     -> [t| Ø |]
  e : es -> [t| $(eType e) :< $(eListType es) |]

stub :: String -> String -> a -> Q b
stub qq fn = const $ fail $ qq ++ ": " ++ fn ++ " not defined."

-- }}}

