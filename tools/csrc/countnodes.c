/* Node count of the stopped search (as tools/emit_cert.count_capped_py, n = 6, stop = 2),
   in GMP (the integer LDL data run to hundreds of bits). Used only to choose certificate
   layouts; the Lean kernel re-walks every node. Returns cap + 1 when the count exceeds cap,
   -1 on bad input. Input: 36 + 6 + 1 integers (a row-major, w, B) in hex, space-separated. */
#include <gmp.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define N 6
static mpz_t A[N][N], W[N], Bk[N + 1], C[N], S[N], T[N], LO[N], HI[N], U[N], Z[N];
static int inited = 0;
static int64_t cnt, capv;

static int rec(int k) { /* Bk[k] holds the bound; returns 1 on cap */
  if (k <= 2) { cnt++; return 0; }
  if (mpz_sgn(Bk[k]) < 0) return 0;
  int i = k - 1;
  mpz_set_ui(C[i], 0);
  for (int j = i + 1; j < N; j++) mpz_addmul(C[i], A[i][j], Z[j]);
  mpz_fdiv_q(S[i], Bk[k], W[i]);
  mpz_sqrt(S[i], S[i]);
  mpz_neg(LO[i], S[i]); mpz_sub(LO[i], LO[i], C[i]); mpz_fdiv_q(LO[i], LO[i], A[i][i]);
  mpz_sub(HI[i], S[i], C[i]); mpz_fdiv_q(HI[i], HI[i], A[i][i]);
  for (mpz_set(T[i], LO[i]); mpz_cmp(T[i], HI[i]) <= 0; mpz_add_ui(T[i], T[i], 1)) {
    if (++cnt > capv) return 1;
    mpz_set(Z[i], T[i]);
    mpz_mul(U[i], A[i][i], T[i]); mpz_add(U[i], U[i], C[i]);
    mpz_mul(U[i], U[i], U[i]);
    mpz_mul(U[i], U[i], W[i]);
    mpz_sub(Bk[i], Bk[k], U[i]);
    if (rec(i)) return 1;
  }
  mpz_set_ui(Z[i], 0);
  return 0;
}

int64_t count_nodes(const char *data, int64_t cap) {
  if (!inited) {
    for (int i = 0; i < N; i++) {
      for (int j = 0; j < N; j++) mpz_init(A[i][j]);
      mpz_init(W[i]); mpz_init(C[i]); mpz_init(S[i]); mpz_init(T[i]);
      mpz_init(LO[i]); mpz_init(HI[i]); mpz_init(U[i]); mpz_init(Z[i]);
    }
    for (int i = 0; i <= N; i++) mpz_init(Bk[i]);
    inited = 1;
  }
  char *buf = strdup(data), *save = NULL, *tok = strtok_r(buf, " ", &save);
  mpz_t *dst[N * N + N + 1];
  int m = 0;
  for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) dst[m++] = &A[i][j];
  for (int i = 0; i < N; i++) dst[m++] = &W[i];
  dst[m++] = &Bk[N];
  for (int r = 0; r < m; r++) {
    if (!tok || mpz_set_str(*dst[r], tok, 16) != 0) { free(buf); return -1; }
    tok = strtok_r(NULL, " ", &save);
  }
  free(buf);
  for (int i = 0; i < N; i++) {
    mpz_set_ui(Z[i], 0);
    if (mpz_sgn(W[i]) <= 0 || mpz_sgn(A[i][i]) <= 0) return -1;
  }
  cnt = 0; capv = cap;
  if (rec(N)) return cap + 1;
  return cnt;
}
