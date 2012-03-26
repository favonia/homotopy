------------------------------------------------------------------------
-- My Code for Homotopy Type Theory 
--
-- Favonia
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

-- A large portion of code was shamelessly copied from Nils' library
-- http://www.cse.chalmers.se/~nad/repos/equality/

{-# OPTIONS --without-K #-}

module README where

------------------------------------------------------------------------
-- Common definitions

import Prelude

------------------------------------------------------------------------
-- Maps, continuous functions between spaces

-- H-iso style equivalence
import Map.Bijection

-- A record with only to & from (no proofs)
import Map.Equivalence

-- Injections
import Map.Injection

-- Surjections
import Map.Surjection

-- Preimage
import Map.Preimage

-- Weak-equivalent
import Map.Weak-equivalence

------------------------------------------------------------------------
-- Paths (propositional equalities in type theories)

-- The definition of paths and trans, subst, cong
import Path

-- Some really basic lemmas for equivalence of paths
import Path.Lemmas

-- Higher-order paths and loops
import Path.Higher-order

-- A short proof that Ω₂(A) is abelian for any space A
import Path.Omega2-abelian

-- Tools to compose/decompose paths in Σ-type
import Path.Sum

-- Tools to manipulate paths in Π-type (extensionality)
--import Path.Prod

-- Definition of H-level and some basic lemmas
--import Path.H-level

------------------------------------------------------------------------
-- Space

-- Kristina's theorem: hom is contractable iff we have a dependent
-- eliminator.
-- (Only the interesting direction.)
import Space.Bool-alternative

-- Definition of integers
import Space.Integer

-- Definition of intervals
import Space.Interval

-- Definition of spheres (base + loop)
import Space.Sphere

-- Alternative definition of spheres (two-point)
import Space.Sphere-alternative

-- Definition of the Hopf junior (S₀ ↪ S₁ → S₁)
-- and a proof that the total space is indeed S₁
import Space.Sphere.Hopf-junior

-- A proof that Ω₁(S₁) is ℤ
import Space.Sphere.Omega1S1-Z

-- Definition of torus
--import Space.Torus

------------------------------------------------------------------------
-- The Univalence axiom

-- Definition of the Univalence axiom
import Univalence

-- A proof that the Univalence axiom implies extensionality for functions
-- Might be moved to Path.Prod later
--import Univalence.Extensionality

-- Some basic lemmas implied by the Univalence axiom
import Univalence.Lemmas

