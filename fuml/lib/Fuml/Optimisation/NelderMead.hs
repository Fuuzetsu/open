{-# LANGUAGE ScopedTypeVariables, RecordWildCards, FlexibleContexts #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file #-}

module Fuml.Optimisation.NelderMead
  ( initialSimplex
  , initialSimplex'
  , solveNm
  ) where

import qualified Data.Vector.Storable as VS
import Data.Vector.Storable (Vector)
import qualified Data.Vector.Storable.Mutable as MVS (unsafeModify)
import qualified Data.Foldable as F
import Data.List (sortBy)
import Data.Ord (comparing)
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import Data.STRef
import Data.Random
import Control.Monad (replicateM, forM, forM_)
import Control.Monad.ST
import Control.Monad.Trans (lift)

type Simplex = [(Vector Double, Double)]

-- | Actual simplex type implementation that we want to use.
type Simplex' = Seq (Vector Double, Double)

centroid :: Simplex' -> Vector Double
centroid e = case Seq.viewl e of
  Seq.EmptyL -> error "Fuml.Optimisation.NelderMead.centroid: empty Simplex input"
  (p, _) Seq.:< ps -> runST $ do
    vec <- VS.thaw p
    lenRef <- newSTRef 1
    let plen = VS.length p
    forM_ ps $ \(v, _) ->
      let vlen = min plen (VS.length v)
          go n | n >= vlen = pure ()
               | otherwise = do
                   MVS.unsafeModify vec (+ v VS.! n) n
                   go (n + 1)
      in go 0
    VS.unsafeFreeze vec

vadd, vsub :: Vector Double -> Vector Double -> Vector Double
vadd = VS.zipWith (+)
vsub = VS.zipWith (-)

sortSimplex :: Simplex -> Simplex
sortSimplex = sortBy (comparing snd)

sortSimplex' :: Simplex' -> Simplex'
sortSimplex' = Seq.sortBy (comparing snd)

shead :: Seq a -> a
shead e = case Seq.viewl e of
  e Seq.:< _ -> e
  Seq.EmptyL -> error "Fuml.Optimisation.NelderMead.shead: empty sequence"

slast :: Seq a -> a
slast e = case Seq.viewr e of
  _ Seq.:> e -> e
  Seq.EmptyR -> error "Fuml.Optimisation.NelderMead.slast: empty sequence"

sinit :: Seq a -> Seq a
sinit e = case Seq.viewr e of
  es Seq.:> _ -> es
  Seq.EmptyR -> error "Fuml.Optimisation.NelderMead.sinit: empty sequence"

initialSimplex :: Monad m => (Vector Double -> m Double)
                          -> Vector Double
                          -> Vector Double
                          -> RVarT m Simplex
initialSimplex f vinit vbox = do
  let gen mid box = uniformT (mid - box) (mid+box)
  initialSimplex' f $ VS.zipWithM gen vinit vbox

initialSimplex' :: Monad m => (Vector Double -> m Double)
                          -> RVarT m (Vector Double)
                          -> RVarT m Simplex
initialSimplex' f vgen = do
  v0 <- vgen
  let n = VS.length v0 + 1
  fmap sortSimplex $ replicateM n $ do
    v <- vgen
    y <- lift $ f v
    return (v, y)

solveNm :: Monad m => (Vector Double -> m Double)
                   -> Simplex
                   -> Double
                   -> Int
                   -> m ([Double], Simplex)
solveNm f s0 tol maxiter = do
  (vs, sim') <- go [] (Seq.fromList s0) 0
  -- Convert simplex back to awful list form that user is used to.
  pure $! (vs, F.toList sim')
  where
    go path sim iter
      | iter > maxiter
        || (iter > maxiter `div` 5
             && abs (snd (shead sim) - snd (slast sim)) < tol)
      = return (path, sim)
      | otherwise = do
          snext <- nmStep f sim
          go (snd (shead snext):path) (sortSimplex' snext) (iter+1)

nmStep :: Monad m => (Vector Double -> m Double) -> Simplex' -> m Simplex'
nmStep f  s0 = do
  let alpha = 1
      gamma = 2
      rho = 0.5
      sigma = 0.5
      x0 = centroid $ sinit s0
      xnp1 = fst (slast s0)
      fxnp1 = snd (slast s0)
      xr = x0 `vadd` (alpha .* (x0 `vsub` xnp1))
      fx1 = snd $ shead s0
  fxr <- f xr

  if fx1 <= fxr && fxr <= (snd $ penultimate s0)
    then return $ swapLast s0 (xr,fxr)
    else do
        let xe = x0 `vadd` (gamma .* (x0 `vsub` xnp1))
        fxe <- f xe
        if fxr < fx1
            then if fxe < fxr
                    then return $ swapLast s0 (xe,fxe)
                    else return $ swapLast s0 (xr,fxr)
            else do
              let xc = xnp1 `vadd` (rho .* (x0 `vsub` xnp1))
              fxc <- f xc
              if fxc < fxnp1
                   then return $ swapLast s0 (xc,fxc)
                   else --reduce
                     case Seq.viewl s0 of
                       p0@(x1,_) Seq.:< rest -> do
                            morePts <- forM rest $ \(xi,_) -> do
                                let xnew = x1 `vadd` (rho .* (xi`vsub`x1))
                                y <- f xnew
                                return (xnew,y)
                            return $ p0 Seq.<| morePts
    where
      penultimate :: Seq a -> a
      penultimate es = case Seq.viewr es of
        es' Seq.:> _ -> case Seq.viewr es' of
          _ Seq.:> e -> e
          Seq.EmptyR ->
            error "Fuml.Optimisation.NelderMead.nmStep.penultimate: nearly empty sequence"
        Seq.EmptyR ->
          error "Fuml.Optimisation.NelderMead.nmStep.penultimate: empty sequence"

      swapLast :: Seq a -> a -> Seq a
      swapLast es newLast = case Seq.viewr es of
        es' Seq.:> _ -> es' Seq.|> newLast
        Seq.EmptyR -> error "Fuml.Optimisation.NelderMead.nmStep.swapLast: empty sequence"

infixr 7 .*
(.*) :: Double -> Vector Double -> Vector Double
x .* v = VS.map (*x) v
