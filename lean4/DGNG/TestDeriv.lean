import Mathlib.Analysis.Calculus.Deriv.Basic

open Real

example (f : ℝ → ℝ × ℝ × ℝ) (h : HasDerivAt f (1,2,3) (0 : ℝ)) : HasDerivAt (fun t => (f t).1) (1 : ℝ) (0 : ℝ) :=
  h.fst

example (f : ℝ → ℝ × ℝ × ℝ) (h : HasDerivAt f (1,2,3) (0 : ℝ)) : HasDerivAt (fun t => (f t).2.1) (2 : ℝ) (0 : ℝ) :=
  h.snd.fst

example (f : ℝ → ℝ × ℝ × ℝ) (h : HasDerivAt f (1,2,3) (0 : ℝ)) : HasDerivAt (fun t => (f t).2.2) (3 : ℝ) (0 : ℝ) :=
  h.snd.snd
