{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

module Type.Family.Monoid where

type family Mempty :: k
type family (a :: k) <> (b :: k) :: k

