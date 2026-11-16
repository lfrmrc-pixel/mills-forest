default(parisizemax, 2000000000);
L = readvec("chain_phi.txt");
{
for (k = 1, #L,
  N = L[k];
  C = read(Str("cert_", k-1, ".gp.txt"));
  if (type(C) == "t_INT",
    r = (C == N && N < 2^64 && ispseudoprime(N) && primecertisvalid(C));
    print("n = ", k-1, ": p_n < 2^64, deterministic BPSW: ", r),
    r = primecertisvalid(C) && C[1][1] == N;
    print("n = ", k-1, ": valid ECPP certificate for p_n: ", r));
);
}
quit;
