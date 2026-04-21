module ProData where

import Data.Profunctor
import Data.Profunctor.Monad
import Data.Prpfunctor.Adjunction

--import Control.Comonad.Trans.Store

import AdjProfunctor

-- newtype ProStore p c a b = ProStore (Store (p a b) c)

data ProData p a b = ProData 
   { proDataPro :: (Data a', Data b') => p a' b'
   , proLArr :: a -> a'
   , proRArr :: b' -> b
   }

instance Profunctor (ProData p) where
   dimap f g pd = pd 
      { proLArr = (proLArr pd) . f
      , proRArr = g . (proRArr pd)
      }


