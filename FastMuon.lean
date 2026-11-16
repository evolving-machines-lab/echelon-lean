import FastMuon.Certificate
import FastMuon.HeadTail
import FastMuon.Cost
import FastMuon.NSPoly
import FastMuon.Spectral
import FastMuon.MuonVsSVD
import FastMuon.Separation
import FastMuon.OptimalTail
import FastMuon.MatrixFacts
import FastMuon.NSMatrix
import FastMuon.Polish

/-!
# FastMuon

Lean proofs for **Echelon**, a rank-`r` replacement for Muon's Newton–Schulz step (its update is a
head on a tracked subspace plus a scaled tail; identifiers keep the older `HeadTail`/`ht_`/`htDir` prefix).
-/
