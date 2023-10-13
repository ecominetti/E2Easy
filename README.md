E2Easy Lattice in-person voting simulator

Code implements a simulator for a voting machine running the E2Easy lattice voting. Commitment and ZKPs primitives are imported from "Lattice-Based Proof of Shuffle and Applications to Electronic Voting" by Diego F. Aranha, Carsten Baum, Kristian Gjøsteen, Tjerand Silde, and Thor Tunge accepted at CT-RSA 2021 (link: https://github.com/dfaranha/lattice-voting-ctrsa21/tree/master), with minor modifications.

Additionaly, the Dilithium reference code (link: https://github.com/pq-crystals/dilithium/tree/master) is used as the signature scheme.

# Modifications to original

The file APISimulator.c contains the modified version of the shuffle code.

These modifications include:
    Shuffle ZKP data is now saved in an output binary file. This file is digitally signed using Dilithium 2.

    Modifications to hash functions calls: FLINT library does not zero the entire data nmod_poly array when nmod_poly_zero is called, only the used MOD part. As a result, when the hash function is called passing the initial memory block location and its size, sometimes some uncleared garbage data is used. This does not result in an error if you call the shuffle prover and shuffle verifier using the same allocated memory, as in the original project. However, if you save the prover data in a file to later verify it, when the data is read and allocated to a different memory block, sometimes the new memory block is includes different garbage data and the verifier hash produces different results. To solve this problem, instead of passing the memory block as the hash argument, the value of each coefficient of the polynomial is retrieved and used as input.


# Instructions to voting

run `make vote` to create voting and spoilCheck

The vote input has to be less than MODP

File voteCom is always created; openingVote is only created if vote is spoiled.
Each new vote rewrites voteCom
voteCom and the correspondent openingVote can be checked using spoilCheck.c (a vote number is used as input; if vote checks returns SUCCESS, otherwise FAIL)

Next voter input has to be 0 or 1

Maximum number of voters allowed is defined in variable VOTERS
