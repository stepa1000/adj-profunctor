module Data.Profunctors.CompPF where

import Data.Profunctor
import Data.Profunctor.Monad
import Data.Prpfunctor.Adjunction
import Data.Distributive
import Data.Profunctor.Composition
import Data.Profunctor.Ran
import Data.Kind

newtype CompPF f g p a b = CompPF {runCompPF :: f (g p) a b}

newtype IdPF p a b = IdPF {runIdPF :: p a b}

instance ProfunctorFunctor IdPF where
   promap f (IdPF p) = IdPF (f p)

instance ProfunctorAdjoint IdPF IdPF where
   unit p = IdPF (IdPF p)
   counit (IdPF (IdPF p)) = p

instance (ProfunctorFunctor f, ProfunctorFunctor g) => ProfunctorFunctor (CompPF f g) where
   promap f (CompPF p) = CompPF $ promap (promap f) p

instance (ProfunctorAdjoint f1 u1, ProfunctorAdjoint f2 u2) 
   => ProfunctorAdjoint (CompPF f2 f1) (CompPF u1 u2) where
   unit p = CompPF $ promap CompPF (unit (unit p))
   counit (CompPF p) = counit (promap counit (RunCompPF p))



