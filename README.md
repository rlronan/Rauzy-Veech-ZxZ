# Rauzy-Veech-ZxZ

Code for computing examples of Rauzy-Veech Induction on (Z^n, <_{lexicographical}).

Currenly computes examples sampled uniformly random from a given bound on coefficients. 

The current implementation provably halts in finite time on all examples, although the upper-bound of the runtime is not currently known, so a hyper-parameter specifies the maximum number of iterations to compute.

Emperically, the overwhelming majority of examples terminate in relatively few steps. 
