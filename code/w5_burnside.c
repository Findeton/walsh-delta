/* Paper XII receipt w5 -- independent Burnside-lemma orbit count.
 *
 * Counts the orbits of Gamma_n = <translations> x GL(n,2) acting on
 * orientations sigma in {+-1}^(2^n - 1), INDEPENDENTLY of the BFS
 * enumeration (receipt w2), by Burnside's lemma:
 *
 *   #orbits = (1 / (2^n |GL(n,2)|)) * sum over (t, M) of #fix(t, M).
 *
 * The element (t, M) acts by sigma_b -> sigma_{M^T b} * chi_b(t).  For a
 * fixed M, let the permutation b -> M^T b of the nonzero masks have c(M)
 * cycles with cycle-XOR values X_1, ..., X_{c(M)} (the XOR of the masks in
 * each cycle).  A sigma fixed by (t, M) exists iff chi_{X_j}(t) = 1 for
 * every cycle (the product of the chi-factors around a cycle must be +1),
 * and then the fixed count is 2^{c(M)} (one free sign per cycle).  Summing
 * over t: the constraint set {t : t perp span(X_j)} has 2^{n - r(M)}
 * elements, r(M) = rank_F2{X_j}.  Hence
 *
 *   #orbits = (1 / (2^n |GL|)) * sum_{M in GL(n,2)} 2^{c(M) + n - r(M)}.
 *
 * This program enumerates ALL invertible n x n matrices over F_2 (checking
 * invertibility by Gaussian elimination), applies the formula, and prints
 * the orbit count for n = 2, 3, 4, 5.  Expected: 2, 4, 14, 176, matching
 * receipt w2 (which is a completeness-checksummed BFS partition).
 *
 * Build:  cc -O2 -o w5_burnside w5_burnside.c    Run: ./w5_burnside
 * (n = 5 enumerates 2^25 candidate matrices; a few seconds.)
 */
#include <stdio.h>
#include <stdint.h>

static int rank_f2(uint32_t *rows, int m, int width)
{
    int r = 0;
    for (int bit = width - 1; bit >= 0 && r < m; bit--) {
        int piv = -1;
        for (int i = r; i < m; i++)
            if (rows[i] >> bit & 1) { piv = i; break; }
        if (piv < 0) continue;
        uint32_t tmp = rows[r]; rows[r] = rows[piv]; rows[piv] = tmp;
        for (int i = 0; i < m; i++)
            if (i != r && (rows[i] >> bit & 1)) rows[i] ^= rows[r];
        r++;
    }
    return r;
}

int main(void)
{
    for (int n = 2; n <= 5; n++) {
        int N = 1 << n, M = N - 1;
        uint64_t total_matrices = 1ull << (n * n);
        unsigned long long gl_count = 0;
        /* accumulate sum of 2^{c + n - r} exactly in 128-bit */
        __uint128_t acc = 0;
        for (uint64_t code = 0; code < total_matrices; code++) {
            uint32_t rows[8];
            for (int i = 0; i < n; i++)
                rows[i] = (uint32_t)((code >> (i * n)) & (uint32_t)(N - 1));
            uint32_t tmp[8];
            for (int i = 0; i < n; i++) tmp[i] = rows[i];
            if (rank_f2(tmp, n, n) != n) continue;   /* not invertible */
            gl_count++;
            /* column masks of the matrix: bit i of (M^T a) = parity(col_i & a) */
            uint32_t col[8];
            for (int i = 0; i < n; i++) {
                col[i] = 0;
                for (int j = 0; j < n; j++)
                    col[i] |= ((rows[j] >> i) & 1u) << j;
            }
            /* permutation a -> M^T a on masks 1..M; cycles + cycle XORs */
            uint32_t seen = 0; /* bitmask over 31 masks (n<=5 so M<=31) */
            uint32_t xors[32]; int c = 0;
            for (int a = 1; a <= M; a++) {
                if (seen >> (a - 1) & 1) continue;
                uint32_t x = 0; int b = a;
                do {
                    seen |= 1u << (b - 1);
                    x ^= (uint32_t)b;
                    int img = 0;
                    for (int i = 0; i < n; i++)
                        img |= (__builtin_parity(col[i] & (uint32_t)b)) << i;
                    b = img;
                } while (b != a);
                xors[c++] = x;
            }
            int r = rank_f2(xors, c, n);
            acc += (__uint128_t)1 << (c + n - r);
        }
        /* orbits = acc / (2^n * gl_count); division must be exact */
        __uint128_t denom = (__uint128_t)gl_count << n;
        unsigned long long orbits = (unsigned long long)(acc / denom);
        unsigned long long rem = (unsigned long long)(acc % denom);
        printf("n=%d: |GL(n,2)|=%llu, orbits=%llu, remainder=%llu %s\n",
               n, gl_count, orbits, rem, rem == 0 ? "OK" : "FAIL");
    }
    return 0;
}
