------------------------------------------------------------------------
-- My Code for Homotopy Type Theory 
--
-- Favonia
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- released under BSD-like license (See LICENSE)

-- A large portion of code was shamelessly copied from Nils Anders Danielsson'
-- library released under BSD-like license (See LICENCE-Nils)
-- http://www.cse.chalmers.se/~nad/repos/equality/
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

module README where

------------------------------------------------------------------------
-- Common definitions

import Prelude

------------------------------------------------------------------------
-- Maps, continuous functions between spaces

-- Homotopy equivalence
import Map.H-equivalence

-- Injections
import Map.Injection

-- Surjections
import Map.Surjection

-- Homotopy Fiber
import Map.H-fiber

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

-- Basic facts about Fin
import Space.Fin.Lemmas

-- Definition of free groups (work in progress)
import Space.FreeGroup

-- Definition of integers
import Space.Integer

-- Definition of intervals
import Space.Interval

-- Basic facts about Fin
import Space.List.Lemmas

-- Some basic facts about Nat
-- (Definition of Nat is in the Prelude)
import Space.Nat.Lemmas

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

