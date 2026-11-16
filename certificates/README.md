# Primality certificates for the chain of A_phi

`chain_phi.txt` lists the primes p_0, ..., p_17 with p_n = floor(A_phi^(phi^n)), A_phi = 5.8311535974..., from 1 to 2735 digits.

- `cert_n.gp.txt`: certificate for p_n produced by `primecert` in PARI/GP 2.19.0. For p_n < 2^64 (n = 0..6) the certificate is p_n itself, and primality follows from BPSW, which is deterministic below 2^64. For n = 7..17 it is an ECPP certificate.
- `cert_n.primo.txt` (n = 7..17): the same certificates exported in Primo format (`primecertexport(C, 1)`), for use with independent verifiers.
- `verify.gp`: run `gp -q verify.gp` in this folder. For each n it reads the certificate, checks it with `primecertisvalid`, and checks that it refers to p_n. All 18 lines print 1.

Producing the certificates took about 14 minutes for p_0..p_16 (685 s for p_16) and about 3.9 hours for p_17 (2735 digits), on a 4-thread laptop. Verification is much faster.
