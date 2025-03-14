{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

#ifndef O_LIQUID
{- LANGUAGE Safe -}
#endif

#if __GLASGOW_HASKELL__ == 810
-- Work around to fix GHC Issue #15304, issue popped up again in GHC 8.10, it should be fixed in GHC 8.12
-- This code is meant to reproduce MR 2608 for GHC 8.10
{-# OPTIONS_GHC -funfolding-keeness-factor=1 -funfolding-use-threshold=80 #-}
#endif

--------------------------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2018-2024 Nathan Waivio
-- License     :  BSD3
-- Maintainer  :  Nathan Waivio <nathan.waivio@gmail.com>
-- Stability   :  Stable
-- Portability :  unportable
--
-- Library implementing standard functions for the Jones Calculus in the Cl3 Library.
-- This implementation of the Jones Calculus is based on the convensions of SPIE's Field Guide to Polarization (ϕ = ω t − k z).
-- 
-- * E. Collett, Field Guide to Polarization, SPIE Field Guides vol. FG05, SPIE (2005). ISBN 0-8194-5868-6.
-- 
--  
-- = Jones Vectors
-- 
-- Within the system of the Bloch Sphere, the Jones Vectors in Cl3 are calculated
-- by generating the left ideal of the rotation of a unit vector to the 'e3' basis.
-- Standard form for for a versor is 'rot = exp $ (-i/2) * theta * u' for angle 'theta'
-- and the rotational axis unit vector 'u'.
--
--          Bloch Sphere Coordinates:
-- 
-- @
--                 e3
--                 |
--                 |____e2
--                / 
--               /
--              e1
-- @
--
--------------------------------------------

module Posit.Cl3.JonesCalculus
(
 -- * Jones Vectors
 hpv, vpv,
 dpv, apv,
 rpv, lpv,
 jv,
 -- * Jones Matrices
 hpm, vpm,
 dpm, apm,
 rpm, lpm,
 jm,
 hpmRot,
 -- * Wave Plates
 qwp, hwp,
 qwpRot, hwpRot,
 wp,
 wpRot,
 -- * Reflection
 refl,
#ifndef O_NO_RANDOM
 -- * Random Jones Vectors
 randJonesVec,
 randOrthogonalJonesVec,
#endif
 -- * Normalization Factorization
 factorize
) where



import Posit.Cl3 ( Cl3( R, V3, I)
                 , dag
                 , bar
                 , toR
                 , toV3
                 , toC
                 , project
                 , randUnitV3 )

-- import Posit hiding (R, phi)
import Posit.Internal.PositC



#ifndef O_NO_RANDOM
-- import safe Algebra.Geometric.Cl3 (randUnitV3)
import System.Random (RandomGen)
#endif

e0 :: PositC es => Cl3 es
e0 = R 1
e1 :: PositC es => Cl3 es
e1 = V3 1 0 0
e2 :: PositC es => Cl3 es
e2 = V3 0 1 0
e3 :: PositC es => Cl3 es
e3 = V3 0 0 1

i :: PositC es => Cl3 es
i = I 1

p1 :: PositF es => Cl3 es
p1 = 0.5 * (e0 + e1)
p2 :: PositF es => Cl3 es
p2 = 0.5 * (e0 + e2)
p3 :: PositF es => Cl3 es
p3 = 0.5 * (e0 + e3)




-- | 'hpv' horizontally polarized Jones vector
hpv :: PositF es => Cl3 es
hpv = signum $ e0 * p3  -- e0 == exp $ (-i/2) * 0 * e2, any vector orthoganl to e3 could have been selected as the rotational axis because the angle is zero

-- | 'vpv' vertically polarized Jones vector
vpv :: PositF es => Cl3 es
vpv = signum $ exp ((-i/2) * pi * e2) * p3  -- e2 is selected to obtain the standard form, e1 or any vector orthoganl to e3 could have been selected

-- | 'dpv' diagonally polarized Jones vector
dpv :: PositF es => Cl3 es
dpv = signum $ exp ((-i/2) * (pi/2) * e2) * p3  -- rotate -e1 to e3 around rotational axis e2, an angle of pi/2

-- | 'apv' anti-diagonally polarized Jones vector
apv :: PositF es => Cl3 es
apv = signum $ exp ((-i/2) * (pi/2) * (-e2)) * p3  -- rotate e1 to e3 around rotational axis -e2, an angle of pi/2

-- | 'rpv' right hand circularly polarized Jones vector
rpv :: PositF es => Cl3 es
rpv = signum $ exp ((-i/2) * (pi/2) * (-e1)) * p3  -- rotate -e2 to e3 around rotational axis -e1, and angle of pi/2

-- | 'lpv' left hand circularly polarized Jones vector
lpv :: PositF es => Cl3 es
lpv = signum $ exp ((-i/2) * (pi/2) * e1) * p3  -- rotate e2 to e3 around rotational axis e1, an angle of pi/2

-- | 'jv' function that returns Jones vector from input vector unit vector
-- currently converts the input to a unit vector
jv (signum.toV3 -> v) | v == e3 = hpv
                      | v == -e3 = vpv
                      | otherwise = signum $ sqrt (e3 * v) * p3


-- | 'hpm' Horizontal Polarizer Jones Matrix
hpm :: PositF es => Cl3 es
hpm = p3

-- | 'vpm' Vertical Polarizer Jones Matrix
vpm :: PositF es => Cl3 es
vpm = bar p3

-- | 'dpm' Diagonal Polarizer Jones Matrix
dpm :: PositF es => Cl3 es
dpm = p1

-- | 'apm' Anti-diagonal Polarizer Jones Matrix
apm :: PositF es => Cl3 es
apm = bar p1

-- | 'rpm' Right Hand Circular Polarizer Jones Matrix
rpm :: PositF es => Cl3 es
rpm = p2

-- | 'lpm' Left Hand Circular Polarizer Jones Matrix
lpm :: PositF es => Cl3 es
lpm = bar p2


-- | 'jm' funciton that returns a Jones Matrix from an input Bloch Vector
-- currently converts the input to a unit vector
jm (signum.toV3 -> v) = project v

-- | 'rot' will produce a versor that rotates a vector by an angle about
-- a unit vector axis.
rot (toR -> theta) (signum.toV3 -> axis) = exp $ (-i/2) * theta * axis

-- | 'rotIsh' will produce a versor that rotates by double the input angle
-- for rotating polarizers and wave plates the axis is e2.
rotIsh (toR -> theta) = rot (2*theta) e2

-- | 'hpmRot' Jones matrix for a rotated ideal Linear Horizontal Polarizer.
-- Input value should be a scalar angle in Radians.
hpmRot (toR -> theta) = 
  let roted = rotIsh theta
  in roted * hpm * dag roted

-- | 'qwp' Quarter Wave Plate Jones Matrix
qwp :: PositF es => Cl3 es
qwp = p3 - i * bar p3

-- | 'qwpRot' Rotated Quarter Wave Plate Jones Matrix.
-- Input value should be a scalar angle in Radians.
qwpRot (toR -> theta) = 
  let roted = rotIsh theta
  in roted * qwp * dag roted

-- | 'hwp' Half Wave Plate Jones Matrix
hwp :: PositF es => Cl3 es
hwp = e3

-- | 'hwpRot' Rotated Half Wave Plate Jones Matrix.
-- Input value should be a scalar angle in Radians.
hwpRot (toR -> theta) = 
  let roted = rotIsh theta
  in roted * hwp * dag roted

-- | 'wp' a Wave Plate with phase shift of phi Jones Matrix.
-- Input value should be a scalar angle in Radians.
wp (toR -> phi) = exp $ (i/2) * phi * e3

-- | 'wpRot' a Rotated Wave Plate with phase shift of phi and rotation theta Jones Matrix.
-- The first input value is phi the phase shift as a scalar value in Radians. The second
-- input value is theta the rotation a scalar angle in Radians.
wpRot (toR -> phi) (toR -> theta) = 
  let roted = rotIsh theta
  in roted * wp phi * dag roted

-- | 'refl' a Refelection Jones Matrix
refl :: PositF es => Cl3 es
refl = e3


-- | 'factorize' is a function that takes an Jones Vector after transformation by an 
-- optical chain, and returns the amplitude (amp), phase (phi), and normalized Jones 
-- Vector (vec), by the factorization of the input such that: @__amp * exp (i*phi/2) * vec__@
factorize :: PositF es => Cl3 es -> (Cl3 es, Cl3 es, Cl3 es)
factorize jonesVec = 
  let c = toC jonesVec
      jonesVec' = recip c * jonesVec
      ampC = abs c
      ampJonesVec' = abs jonesVec'
      normJonesVec = recip ampJonesVec' * jonesVec'
      amp = ampC * ampJonesVec'
      normC = recip ampC * c
      phi = 2 * (-i) * log normC
  in (amp, phi, normJonesVec)

#ifndef O_NO_RANDOM
-------------------------------------------------------------------
--
--  Random Jones Vectors
--
-------------------------------------------------------------------

-- | 'randJonesVec' a Random Jones Vector.
randJonesVec :: (PositF es, RandomGen g) => g -> (Cl3 es, g)
randJonesVec g =
  let (v3, g') = randUnitV3 g
  in (jv v3,g')

-- | 'randOrthogonalJonesVec' a Random Orthogonal Complementary pair of Jones
-- Vectors.
randOrthogonalJonesVec :: (PositF es, RandomGen g) => g -> ((Cl3 es, Cl3 es), g)
randOrthogonalJonesVec g = 
  let (v3, g') = randUnitV3 g
  in ((jv v3, jv (bar v3)),g')

#endif
