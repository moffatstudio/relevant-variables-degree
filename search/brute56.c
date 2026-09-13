/*
 * brute56.c -- independent brute force for n = 5 and n = 6, using NOTHING but the definition:
 *   count Boolean functions f : {-1,1}^n -> {-1,1} of Fourier degree <= 3 with all n variables relevant.
 *
 * n = 5:  enumerate all 2^32 functions (Gray code, fixing f(0) = +1 and doubling at the end), maintaining
 *         the six Fourier sums  s_S = sum_x f(x) chi_S(x)  for |S| >= 4 incrementally; degree <= 3 iff all six
 *         vanish.  Every degree-<=3 function (relevant or not) is stored.
 * n = 6:  f(x, x6) = f0(x) [x6 = -1], f1(x) [x6 = +1].  Both restrictions have degree <= 3 on 5 variables and
 *         f has degree <= 3 iff additionally deg(f1 - f0) <= 2, i.e. f0 and f1 have identical degree-3 Fourier
 *         coefficients.  So group the stored 5-variable functions (and their negatives) by their ten degree-3
 *         sums and count ordered pairs (f0, f1) in the same group with f0 != f1 (x6 relevant) and every
 *         x1..x5 relevant in f0 or f1.
 * Output: labelled counts, to be compared with  sum over search orbits of |orbit|  (orbit_count.py).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int chi(uint32_t x, int S) { return (__builtin_popcount(x & S) & 1) ? -1 : 1; }

static uint32_t *D; static size_t Dn = 0, Dcap = 0;
static void push(uint32_t f) { if (Dn == Dcap) { Dcap = Dcap ? 2 * Dcap : 1 << 16; D = realloc(D, Dcap * sizeof *D); } D[Dn++] = f; }

static int relevant(uint32_t f, int i) { /* 5-variable function given as 32-bit mask: bit x set <=> f(x) = -1 */
    uint32_t g = 0; for (uint32_t x = 0; x < 32; x++) if (f >> (x ^ (1u << i)) & 1) g |= 1u << x;
    return g != f;
}

typedef struct { int32_t key[10]; uint32_t f; uint8_t rel; } ent_t;
static int cmp(const void *a, const void *b) { return memcmp(((const ent_t *)a)->key, ((const ent_t *)b)->key, sizeof(int32_t) * 10); }

int main(void) {
    clock_t t0 = clock();
    /* ---- n = 5 ---- */
    int hi[6], nh = 0;
    for (int S = 0; S < 32; S++) if (__builtin_popcount(S) >= 4) hi[nh++] = S;
    int fval[32]; for (int x = 0; x < 32; x++) fval[x] = 1;         /* start: f == +1 */
    long long s[6]; for (int k = 0; k < 6; k++) { s[k] = 0; for (int x = 0; x < 32; x++) s[k] += chi(x, hi[k]); }
    uint32_t fmask = 0;                                               /* bit x set <=> f(x) = -1 */
    long long deg3 = 0, rel5 = 0;
    /* Gray code over bits 1..31 (bit 0 = f(0) fixed to +1) : 2^31 functions */
    for (uint32_t i = 0; ; i++) {
        int ok = 1; for (int k = 0; k < 6; k++) if (s[k]) { ok = 0; break; }
        if (ok) {
            deg3++; push(fmask);
            int r = 1; for (int v = 0; v < 5 && r; v++) if (!relevant(fmask, v)) r = 0;
            if (r) rel5++;
        }
        if (i == 0x7fffffffu) break;
        uint32_t j = i + 1; int k = __builtin_ctz(j) + 1;            /* flip point k (1..31) */
        int old = fval[k]; fval[k] = -old; fmask ^= 1u << k;
        for (int t = 0; t < 6; t++) s[t] += -2 * old * chi(k, hi[t]);
    }
    printf("n=5: degree<=3 Boolean functions with f(0)=+1: %lld  (x2 = %lld total); with all 5 relevant: %lld (x2 = %lld labelled)\n",
           deg3, 2 * deg3, rel5, 2 * rel5);
    fflush(stdout);
    /* ---- n = 6 ---- */
    int d3[10], nd = 0; for (int S = 0; S < 32; S++) if (__builtin_popcount(S) == 3) d3[nd++] = S;
    size_t M = 2 * Dn; ent_t *E = malloc(M * sizeof *E);
    for (size_t a = 0; a < Dn; a++) for (int sg = 0; sg < 2; sg++) {
        uint32_t f = sg ? ~D[a] : D[a]; ent_t *e = &E[2 * a + sg]; e->f = f;
        for (int t = 0; t < 10; t++) { int32_t v = 0; for (uint32_t x = 0; x < 32; x++) v += ((f >> x & 1) ? -1 : 1) * chi(x, d3[t]); e->key[t] = v; }
        e->rel = 0; for (int v = 0; v < 5; v++) if (relevant(f, v)) e->rel |= 1 << v;
    }
    qsort(E, M, sizeof *E, cmp);
    long long pairs = 0, groups = 0; size_t maxg = 0;
    for (size_t a = 0; a < M;) {
        size_t b = a; while (b < M && cmp(&E[a], &E[b]) == 0) b++;
        groups++; if (b - a > maxg) maxg = b - a;
        for (size_t p = a; p < b; p++) for (size_t q = a; q < b; q++)
            if (E[p].f != E[q].f && (E[p].rel | E[q].rel) == 31) pairs++;
        a = b;
    }
    printf("n=6: labelled degree<=3 Boolean functions with all 6 relevant: %lld   (%lld key-groups, largest %zu)\n", pairs, groups, maxg);
    printf("time %.1fs\n", (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
