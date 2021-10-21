# Attacks on range proofs in MtA

This project is a proof-of-concept for the missing range proof attack on threshold ECDSA protocols [GG18](https://eprint.iacr.org/2019/114.pdf) and [GG20](https://eprint.iacr.org/2020/540.pdf).
The details of this attack are presented in our [paper](TODO: link), section 2.2.

The value of `M` used in the code is `2^16`, leading to key leakage in 16 signatures, which can be improved upon by choosing larger values of `M`.
For `M=2^29` and key leakage in 8 signatures, my laptop would have to work for about 2 days, i.e. it's completely possible, as most of the 
computation is done before the attack and no computation is needed during or between signatures.

Presented vulnerability was fixed in [this commit](TODO: link to the commit).

## Run it

To run the project, [gmp](https://gmplib.org) is required. After cloning, run

`cargo test large_k_attack -- --nocapture`