# formalized-proof-mining
Lean implementation of Gödel's Dialectica intepretation and a general metatheorem for proof mining, of the form of those introduced by Kohlenbach.


It is basee on the implementation of Dialectica in Coq done by Andrej Bauer,http://math.andrej.com/2011/01/03/the-dialectica-interpertation-in-coq/

We define a shallow embedding into Lean of the simple types from Gödel's T.
Based on it, FOL formulas are then given a HOAS representation.
We construct and prove the correctness of realizers for the axioms and rules in our logical system, thereby proving the soundness theorem.
Finally, we use the result for proving a proof mining-like metatheorem on term extraction from proofs.

Bauer remarked the necessity of a number of departures from the standard Dialectica into a more depenently typed one when using this encoding, and they apply to our implementation too.

