{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
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
-- A 'QuasiQuoter' for the 'Index' type.
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

module Data.Type.Index.Quote
  ( ix
  ) where

import Data.Type.Index
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Text.Read (readMaybe)
import Control.Monad
import Data.Maybe (maybeToList)

ix :: QuasiQuoter
ix = QuasiQuoter
  { quoteExp  = parseIxExp
  , quotePat  = parseIxPat
  , quoteType = error "ix: quoteType not defined"
  , quoteDec  = error "ix: quoteDec not defined"
  }

data IndexExp
  = I Int
  | A String Int
  deriving (Eq,Ord,Show)

instance Read IndexExp where
  readsPrec d = readParen (d > 10) $ \s0 ->
    [ (A x i,s3)
    | (x,s1)    <- lex s0
    , ("+",s2) <- lex s1
    , (n,s3)   <- lex s2
    , i <- maybeToList $ readMaybe n
    ] ++
    [ (I i,s1)
    | (n,s1) <- lex s0
    , i <- maybeToList $ readMaybe n
    ]

parseIxExp :: String -> Q Exp
parseIxExp s = maybe (fail $ "ix: couldn't parse index expression: " ++ show s)
  (notNeg >=> go)
  $ readMaybe s
  where
  notNeg :: IndexExp -> Q IndexExp
  notNeg e = case e of
    I n | n < 0 -> fail $ "ix: negative index: " ++ show n
        | True  -> return e
    A _ n
        | n < 0 -> fail $ "ix: negative index: " ++ show n 
        | True  -> return e
  go :: IndexExp -> Q Exp
  go = \case
    I 0   -> [| IZ |]
    I n   -> [| IS $(go $ I $ n-1) |]
    A x 0 -> varE $ mkName x
    A x n -> [| IS $(go $ A x $ n-1) |]

parseIxPat :: String -> Q Pat
parseIxPat s = maybe (fail $ "ix: couldn't parse Int: " ++ show s)
  (notNeg >=> go)
  $ readMaybe s
  where
  notNeg :: IndexExp -> Q IndexExp
  notNeg e = case e of
    I n | n < 0 -> fail $ "ix: negative index: " ++ show n
        | True  -> return e
    A _ n
        | n < 0 -> fail $ "ix: negative index: " ++ show n 
        | True  -> return e
  go :: IndexExp -> Q Pat
  go = \case
    I 0   -> [p| IZ |]
    I n   -> [p| IS $(go $ I $ n-1) |]
    A x 0 -> varP $ mkName x
    A x n -> [p| IS $(go $ A x $ n-1) |]

{-
-- IxPerm {{{

ixPerm :: QuasiQuoter
ixPerm = QuasiQuoter
  { quoteExp  = parsePerm >=> mkIxPerm
  , quotePat  = error "ixPerm: quotePat not provided"
  , quoteType = error "ixPerm: quoteType not provided"
  , quoteDec  = error "ixPerm: quoteDec not provided"
  }

parsePerm :: String -> Q [Int]
parsePerm s = case traverse readMaybe ws of
  Nothing -> fail $ "perm: expected space-separated sequence of natural numbers: " ++ unwords ws
  Just xs | null missing -> return xs
          | any (< 0) xs     -> fail $ "negative indices: " ++ show xs
          | otherwise    -> fail $ "missing indices: " ++ show missing
    where
    missing = filter (not . (`elem` xs)) ns
  where
  ws = words s
  ns = [0..(length ws - 1)]

mkIxPerm :: [Int] -> Q Exp
mkIxPerm is
  | n == 0 = [| Perm id |]
  | True   = do
    x   <- newName "x"
    nms <- replicateM n $ newName "a"
    let (ns,eps) = go 0 nms is
        (as,bs) = unzip ns
        (brsTo,brsFrom) = unzip
          [ ( match p1 (normalB e2) []
            , match p2 (normalB e1) []
            )
          | ((e1,p1),(e2,p2)) <- eps
          ]
        toFn = [| $( lamCaseE brsTo ) :: $( bindTy nms $ mkPerTy x as bs ) |]
        fromFn = [| $( lamCaseE brsFrom ) :: $( bindTy nms $ mkPerTy x bs as ) |]
    [| Perm ( $toFn <-> $fromFn ) |]
  where
  bindTy ns = forallT (plainTV <$> ns) $ return []
  mkPerTy x as bs = [t| Index $(promotedListT $ varT <$> as) $(varT x) <-> Index $(promotedListT $ varT <$> bs) $(varT x) |]
  n = length is
  badE = [| error "impossible" |]
  go :: Int -> [Name] -> [Int] -> ([(Name,Name)],[((ExpQ,PatQ),(ExpQ,PatQ))])
  go i nms = \case
    x : xs -> ((nms !! i,nms !! x) :) *** ((mkIx i,mkIx x) :) $ go (i+1) nms xs
    _      -> ([],[((badE,wildP),(badE,wildP))])

promotedListT :: [TypeQ] -> TypeQ
promotedListT = foldr (\a as -> promotedConsT `appT` a `appT` as) promotedNilT

mkIx :: Int -> (ExpQ,PatQ)
mkIx n | n <= 0 = ([| IZ |],[p| IZ |])
       | True   = ([| IS $e |],[p| IS $p |])
  where
  (e,p) = mkIx $ n - 1

-- }}}
-}

