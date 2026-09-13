/*
 * r3search.c -- complete search for coefficient vectors N : {S subset [n], |S|<=3} -> Z with
 *   (i)   sum_S n_S^2 = 16
 *   (ii)  f_N^2 == 1 on {-1,1}^n, where 4 f_N = sum_S n_S chi_S
 *   (iii) every variable relevant.
 *
 * Method: orderly generation vertex by vertex.  Processing vertex v fixes every set S containing v.
 * The "link" of v is L_v = 4 D_v f_N = sum_{S ∋ v} n_S chi_{S\v}, a degree-<=2 integer polynomial on
 * the other variables.  By E1 it takes values in {0,+-4}; by E2 its mass m_v = sum_{S∋v} n_S^2 lies
 * in [4,16].  At step v the part of L_v involving an already processed variable is fixed; the rest
 * (terms inside {v+1..n-1}) is enumerated by a DFS with the following NECESSARY-condition prunes only:
 *   P1 budget:   used mass + new mass <= 16, m_v <= 16.
 *   P2 bounded conditional expectations: for any set A of variables, E[L_v | x_A] is the sum of the
 *                terms of L_v inside A, and since L_v in {0,+-4} this partial sum is bounded by 4.
 *   P3 weighted degree: for a variable w of the link, D_w L_v = 4 D_w D_v f_N is an affine integer
 *                polynomial with values in {0,+-2,+-4} (a-b, a+b in {0,+-4} => b in {0,+-2,+-4}),
 *                hence |const| + sum |coeffs| <= 4, i.e. sum_{T ∋ w} |c_T| <= 4 (also for partial sums).
 *   P4 needs:    each not-yet-processed vertex u needs m_u >= 4 (E2); every future set contributes its
 *                n_S^2 to at most 3 vertices, so sum_u max(0, 4 - mass_u) <= 3 * (16 - used).
 * Symmetry (E3 only): "fresh" variables (unprocessed, appearing in no fixed nonzero set) may be permuted
 * and negated freely, and a vertex whose link has no fixed part may be negated (global sign of its link)
 * and swapped with any fresh vertex.  We require: fresh labels are introduced in order (rule R), the
 * completion is lexicographically minimal among its images under Sym(fresh used) x sign flips that
 * satisfy R, and (when the link has no fixed part) m_v >= m_u for fresh u (enforced through caps).
 * Every solution has an image under E3 satisfying all of these, so the search is complete.
 * At the last vertex the full condition (ii) is checked pointwise (2^n points) -- E1 is only a prune.
 *
 * Modes:  r3search N            full search for n = N (prints every solution found, one per line)
 *         r3search -links K M   catalogue: all valid links on <= K variables with mass in [4,M],
 *                               one per orbit of Sym(K) x flips x global sign.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 13
#define MAXPTS (1 << (MAXN - 1))

static int n;                    /* number of vertices */
static int catmode = 0;          /* catalogue mode */
static int MASSMAX = 16;         /* max mass of a link */
static int coef[1 << MAXN];      /* n_S indexed by bitmask */
static int mass[MAXN];           /* fixed mass of each vertex */
static int cap[MAXN];            /* upper bound on m_u from fresh-vertex symmetry */
static int used_total;           /* sum of fixed n_S^2 */
static long long nodes, links_done, leaves, solutions, cand_links[MAXN];
static long long canon_rejects;

/* per-step state */
static int V;                    /* vertex being processed */
static int wdeg[MAXN];           /* weighted degree inside L_V, by variable */
static int isfresh[MAXN];        /* fresh flags at start of step V (for u > V) */
static int Pzero;                /* fixed part of L_V identically zero (as coefficients) */
static int Pmass;                /* mass of fixed part */
static int qmass;                /* mass of completion so far */
static int8_t g[MAXN][MAXN][MAXPTS];   /* g[V][d] : partial link of step V over positions 0..d-1 (per-step buffers!) */
static int8_t ellbuf[MAXN][MAXN][MAXPTS];
static int splitK = 1, splitI = 0;     /* optional split of the step-0 links across processes */

/* saved per-step context for recursion between steps */
typedef struct { int V, wdeg[MAXN], isfresh[MAXN], Pzero, Pmass, qmass, NFmask; } ctx_t;

static void step(int v);

static inline int sgnbit(int x, int pmask) { return (__builtin_popcount(x & pmask) & 1) ? -1 : 1; }
static inline int iabs(int a) { return a < 0 ? -a : a; }
static inline int popc(int x) { return __builtin_popcount(x); }

/* position of variable u in the link of V : u<V -> u ; u>V -> u-1 */
static inline int pos_of(int u) { return u < V ? u : u - 1; }

static int budget_left(void) {
    int b1 = 16 - used_total - qmass;
    int b2 = MASSMAX - Pmass - qmass;
    if (cap[V] - Pmass - qmass < b2) b2 = cap[V] - Pmass - qmass;
    return b1 < b2 ? b1 : b2;
}

/* ---------- canonicity of the completion Q at the end of a link ---------- */
static int Wlist[MAXN], Wn;           /* used fresh labels, ascending */
static int qterm_mask[128], qterm_n;   /* all candidate Q terms S (with bit V), ascending mask */
static int NFmask;                    /* non-fresh link variables (processed or unprocessed with mass>0) */

/* R holds for labelled completion given by perm sigma on W (sigma maps old label -> new label).
   We check on the ORIGINAL Q: new label f_t = Wlist[t] corresponds to old variable inv[t]. */
static int check_R_perm(const int *inv /* inv[t] = old var sitting at new label Wlist[t] */) {
    for (int t = 0; t < Wn; t++) {
        int u = inv[t];
        int ok = 0;
        /* allowed partners (old labels): NF, inv[0..t-1], inv[t+1] */
        int allowed = NFmask;
        for (int s = 0; s < t; s++) allowed |= 1 << inv[s];
        if (t + 1 < Wn) allowed |= 1 << inv[t + 1];
        /* singleton term {V,u} */
        if (coef[(1 << V) | (1 << u)]) ok = 1;
        for (int y = V + 1; y < n && !ok; y++) {
            if (y == u) continue;
            if (coef[(1 << V) | (1 << u) | (1 << y)] && (allowed >> y & 1)) ok = 1;
        }
        if (!ok) return 0;
    }
    return 1;
}

/* lexicographic comparison: is image (sigma, flips) < Q ?  Return -1 if image < Q, 0 equal, 1 greater. */
static int perm_map[MAXN];  /* old label -> new label */
static int compare_image(int flipmask /* bit over new labels + bit MAXN for global */) {
    int global = (flipmask >> MAXN) & 1;
    /* image coefficient at term S' = sign * coef[sigma^{-1}(S')].  We iterate over terms S' in ascending
       mask order; sigma^{-1}(S') = apply inverse perm.  Build inverse map once per perm (done by caller). */
    extern int inv_map[MAXN];
    for (int t = 0; t < qterm_n; t++) {
        int Sp = qterm_mask[t];
        /* preimage */
        int S = 0, m = Sp;
        while (m) { int b = __builtin_ctz(m); m &= m - 1; S |= 1 << inv_map[b]; }
        int c = coef[S];
        int sgn = global ? -1 : 1;
        if (popc(Sp & flipmask & ((1 << MAXN) - 1)) & 1) sgn = -sgn;
        int ci = c * sgn;
        int cq = coef[Sp];
        if (ci < cq) return -1;
        if (ci > cq) return 1;
    }
    return 0;
}
int inv_map[MAXN];

static int perm_arr[MAXN];
/* recursive enumeration of permutations of W; returns 0 if a smaller R-image found */
static int perm_rec(int t, int usedmask) {
    if (t == Wn) {
        /* perm_arr[t] = old variable placed at new label Wlist[t] */
        for (int u = 0; u < n; u++) { perm_map[u] = u; inv_map[u] = u; }
        for (int s = 0; s < Wn; s++) { perm_map[perm_arr[s]] = Wlist[s]; inv_map[Wlist[s]] = perm_arr[s]; }
        if (!check_R_perm(perm_arr)) return 1;
        int Wm = 0; for (int s = 0; s < Wn; s++) Wm |= 1 << Wlist[s];
        /* enumerate flips over new labels in W (and global if Pzero) */
        int nflip = 1 << Wn;
        for (int gl = 0; gl <= (Pzero ? 1 : 0); gl++) {
            for (int f = 0; f < nflip; f++) {
                int fm = 0; for (int s = 0; s < Wn; s++) if (f >> s & 1) fm |= 1 << Wlist[s];
                if (gl) fm |= 1 << MAXN;
                if (compare_image(fm) < 0) return 0;
            }
        }
        return 1;
    }
    for (int s = 0; s < Wn; s++) {
        if (usedmask >> s & 1) continue;
        perm_arr[t] = Wlist[s];
        if (!perm_rec(t + 1, usedmask | (1 << s))) return 0;
    }
    return 1;
}

static int is_canonical(void) {
    /* used fresh labels */
    Wn = 0;
    for (int u = V + 1; u < n; u++) if (isfresh[u] && wdeg[u] > 0) Wlist[Wn++] = u;
    /* exact R check for Q itself (identity perm) */
    for (int s = 0; s < Wn; s++) perm_arr[s] = Wlist[s];
    if (!check_R_perm(perm_arr)) return 0;
    /* prefix: used fresh labels must be the first Wn fresh labels */
    int cnt = 0;
    for (int u = V + 1; u < n; u++) {
        if (!isfresh[u]) continue;
        if (cnt < Wn) { if (Wlist[cnt] != u) return 0; cnt++; }
    }
    /* term index space */
    qterm_n = 0;
    for (int S = 0; S < (1 << n); S++) {
        if (!(S >> V & 1)) continue;
        if (S & ((1 << V) - 1)) continue;
        if (popc(S) > 3) continue;
        qterm_mask[qterm_n++] = S;
    }
    return perm_rec(0, 0);
}

/* ---------- final check of a complete coefficient vector ---------- */
static void final_check(void) {
    leaves++;
    if (used_total != 16) return;
    /* (ii): 4 f_N in {+-4} at all 2^n points */
    int terms[64], tc[64], nt = 0;
    for (int S = 0; S < (1 << n); S++) if (coef[S] && popc(S) <= 3) { terms[nt] = S; tc[nt] = coef[S]; nt++; }
    for (int x = 0; x < (1 << n); x++) {
        int s = 0;
        for (int t = 0; t < nt; t++) s += tc[t] * sgnbit(x, terms[t]);
        if (s != 4 && s != -4) return;
    }
    for (int i = 0; i < n; i++) if (mass[i] < 4) return; /* (iii) -- always true here */
    solutions++;
    printf("SOL");
    for (int t = 0; t < nt; t++) {
        printf(" ");
        int S = terms[t], first = 1;
        if (!S) printf("e");
        for (int i = 0; i < n; i++) if (S >> i & 1) { printf("%s%d", first ? "" : ",", i + 1); first = 0; }
        printf(":%d", tc[t]);
    }
    printf("\n");
    fflush(stdout);
}

/* ---------- end of a link ---------- */
static void print_link(void) {
    /* catalogue line: mass nvars terms... (terms as subsets of link labels 1..K, coefficient) */
    int nv = 0; for (int u = 1; u < n; u++) if (wdeg[u] > 0) nv++;
    printf("LINK m=%d k=%d", Pmass + qmass, nv);
    for (int S = 0; S < (1 << n); S++) {
        if (!(S & 1) || popc(S) > 3 || !coef[S]) continue;
        printf(" ");
        int T = S >> 1, first = 1;
        if (!T) printf("e");
        for (int i = 0; i < n; i++) if (T >> i & 1) { printf("%s%d", first ? "" : ",", i + 1); first = 0; }
        printf(":%d", coef[S]);
    }
    printf("\n");
}

static void finish_link(void) {
    links_done++;
    int d = n - 1, npts = 1 << d;
    for (int x = 0; x < npts; x++) { int a = g[V][d][x]; if (a != 0 && a != 4 && a != -4) return; }
    int mv = Pmass + qmass;
    if (mv < 4 || mv > cap[V] || mv > MASSMAX) return;
    /* pending fresh labels must be resolved: exact R + lex-min canonicity */
    if (!is_canonical()) { canon_rejects++; return; }
    cand_links[V]++;
    if (catmode) { print_link(); return; }
    if (V == 0 && splitK > 1 && ((cand_links[0] - 1) % splitK) != splitI) return;
    /* commit */
    int newmass[MAXN]; memcpy(newmass, mass, sizeof(mass));
    for (int S = 0; S < (1 << n); S++) {
        if (!(S >> V & 1) || (S & ((1 << V) - 1)) || popc(S) > 3 || !coef[S]) continue;
        int c2 = coef[S] * coef[S];
        for (int u = 0; u < n; u++) if (S >> u & 1) newmass[u] += c2;
    }
    int R = 16 - used_total - qmass;
    if (R < 0) return;
    int needs = 0;
    for (int u = V + 1; u < n; u++) { int nd = 4 - newmass[u]; if (nd > 0) { needs += nd; if (nd > R) return; } }
    if (needs > 3 * R) return;
    if (V == n - 1 && R != 0) return;
    /* save & recurse */
    int savemass[MAXN], savecap[MAXN]; memcpy(savemass, mass, sizeof(mass)); memcpy(savecap, cap, sizeof(cap));
    memcpy(mass, newmass, sizeof(mass));
    used_total += qmass;
    if (Pzero) for (int u = V + 1; u < n; u++) if (isfresh[u] && cap[u] > mv) cap[u] = mv;
    ctx_t save; save.V = V; memcpy(save.wdeg, wdeg, sizeof(wdeg)); memcpy(save.isfresh, isfresh, sizeof(isfresh));
    save.Pzero = Pzero; save.Pmass = Pmass; save.qmass = qmass; save.NFmask = NFmask;
    step(V + 1);
    V = save.V; memcpy(wdeg, save.wdeg, sizeof(wdeg)); memcpy(isfresh, save.isfresh, sizeof(isfresh));
    Pzero = save.Pzero; Pmass = save.Pmass; qmass = save.qmass; NFmask = save.NFmask;
    used_total -= qmass;
    memcpy(mass, savemass, sizeof(mass)); memcpy(cap, savecap, sizeof(cap));
}

/* ---------- group DFS ---------- */
static void do_group(int u);

/* after finishing group u (u fresh): pending fresh labels a < u need a non-fresh partner y > u */
static int pending_ok(int u) {
    int pend = 0;
    for (int a = V + 1; a < u; a++) if (isfresh[a] && wdeg[a] == 0) pend++;
    if (!pend) return 1;
    int nf = 0;
    for (int y = u + 1; y < n; y++) if (!isfresh[y] && wdeg[y] < 4) nf++;
    if (!nf) return 0;
    if (pend > budget_left()) return 0;
    return 1;
}

static void ell_dfs(int u, int w) {
    int d = u - 1, npts = 1 << d;
    int8_t *ell = ellbuf[V][d], *gg = g[V][d];
    if (w == u) {
        /* constant term of ell : S = {V,u} */
        int S = (1 << V) | (1 << u);
        int cmax = 4 - wdeg[u];
        int b = budget_left();
        for (int c = -cmax; c <= cmax; c++) {
            if (c * c > b) continue;
            int ok = 1;
            for (int x = 0; x < npts; x++) { int l = ell[x] + c; if (l < 0) l = -l; int a = gg[x]; if (a < 0) a = -a; if (l > 4 - a) { ok = 0; break; } }
            if (!ok) continue;
            nodes++;
            coef[S] = c; wdeg[u] += iabs(c); qmass += c * c;
            int8_t *gn = g[V][d + 1];
            for (int x = 0; x < npts; x++) { int l = ell[x] + c; gn[x] = gg[x] + l; gn[x | npts] = gg[x] - l; }
            if (!isfresh[u] || wdeg[u] == 0 || pending_ok(u)) do_group(u + 1);
            coef[S] = 0; wdeg[u] -= iabs(c); qmass -= c * c;
        }
        return;
    }
    /* free pair term S = {V, w, u}, variable w at position w-1 */
    int S = (1 << V) | (1 << w) | (1 << u);
    int cmax = 4 - wdeg[u]; if (4 - wdeg[w] < cmax) cmax = 4 - wdeg[w];
    int b = budget_left();
    int pm = 1 << (w - 1);
    /* c = 0 */
    ell_dfs(u, w + 1);
    for (int c = -cmax; c <= cmax; c++) {
        if (c == 0 || c * c > b) continue;
        int rem = 4 - wdeg[u] - iabs(c);  /* remaining weight allowance for u */
        int ok = 1;
        for (int x = 0; x < npts; x++) {
            int l = ell[x] + c * sgnbit(x, pm); if (l < 0) l = -l;
            int a = gg[x]; if (a < 0) a = -a;
            if (l > 4 - a + rem) { ok = 0; break; }
        }
        if (!ok) continue;
        for (int x = 0; x < npts; x++) ell[x] += c * sgnbit(x, pm);
        coef[S] = c; wdeg[u] += iabs(c); wdeg[w] += iabs(c); qmass += c * c;
        ell_dfs(u, w + 1);
        coef[S] = 0; wdeg[u] -= iabs(c); wdeg[w] -= iabs(c); qmass -= c * c;
        for (int x = 0; x < npts; x++) ell[x] -= c * sgnbit(x, pm);
    }
}

static void do_group(int u) {
    if (u == n) { finish_link(); return; }
    int d = u - 1, npts = 1 << d;
    int8_t *ell = ellbuf[V][d];
    memset(ell, 0, npts);
    /* fixed part: terms {i,u,V}, i < V */
    for (int i = 0; i < V; i++) {
        int c = coef[(1 << i) | (1 << u) | (1 << V)];
        if (!c) continue;
        for (int x = 0; x < npts; x++) ell[x] += c * sgnbit(x, 1 << i);
    }
    ell_dfs(u, V + 1);
}

static void step(int v) {
    if (v == n) { final_check(); return; }
    V = v;
    /* fresh flags */
    for (int u = 0; u < n; u++) isfresh[u] = (u > V && mass[u] == 0);
    /* non-fresh mask for R */
    NFmask = 0;
    for (int u = 0; u < n; u++) if (u != V && !isfresh[u]) NFmask |= 1 << u;
    /* fixed part P */
    memset(wdeg, 0, sizeof(wdeg));
    Pmass = 0; Pzero = 1; qmass = 0;
    int low = (1 << V) - 1;
    for (int S = 0; S < (1 << n); S++) {
        if (!(S >> V & 1) || !(S & low) || popc(S) > 3) continue;
        int c = coef[S];
        if (!c) continue;
        Pzero = 0; Pmass += c * c;
        for (int u = 0; u < n; u++) if (u != V && (S >> u & 1)) wdeg[u] += iabs(c);
    }
    for (int u = 0; u < n; u++) if (wdeg[u] > 4) return;        /* P3 */
    if (Pmass > cap[V] || Pmass > MASSMAX) return;
    /* initial g over positions 0..V-1 : P-terms inside {0..V-1} */
    int npts = 1 << V;
    int8_t *g0 = g[V][V];
    memset(g0, 0, npts);
    for (int S = 0; S < (1 << n); S++) {
        if (!(S >> V & 1) || !(S & low) || popc(S) > 3) continue;
        if (S & ~(low | (1 << V))) continue;   /* must be inside {0..V-1} ∪ {V} */
        int c = coef[S]; if (!c) continue;
        int T = S & low;
        for (int x = 0; x < npts; x++) g0[x] += c * sgnbit(x, T);
    }
    /* constant term c_∅ : S = {V} */
    int S0 = 1 << V;
    int b = budget_left();
    for (int c = -4; c <= 4; c++) {
        if (c * c > b) continue;
        int ok = 1;
        for (int x = 0; x < npts; x++) { int a = g0[x] + c; if (a > 4 || a < -4) { ok = 0; break; } }  /* P2 */
        if (!ok) continue;
        for (int x = 0; x < npts; x++) g0[x] += c;
        coef[S0] = c; qmass += c * c;
        do_group(V + 1);
        coef[S0] = 0; qmass -= c * c;
        for (int x = 0; x < npts; x++) g0[x] -= c;
    }
}

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "-links") == 0) {
        catmode = 1;
        int K = atoi(argv[2]); MASSMAX = atoi(argv[3]);
        n = K + 1;
    } else if (argc >= 2) {
        n = atoi(argv[1]);
        for (int a = 2; a < argc; a++) {
            if (strcmp(argv[a], "-split") == 0 && a + 2 < argc) { splitK = atoi(argv[a + 1]); splitI = atoi(argv[a + 2]); a += 2; }
            else MASSMAX = atoi(argv[a]);
        }
    } else { fprintf(stderr, "usage: r3search2 N [MASSMAX] [-split K I] | r3search2 -links K M\n"); return 1; }
    if (n > MAXN) { fprintf(stderr, "n too large\n"); return 1; }
    for (int i = 0; i < n; i++) cap[i] = MASSMAX;
    clock_t t0 = clock();
    /* constant term n_empty: never touched by the vertex steps (it lies in no link).  By the global sign
       symmetry N -> -N (E3), which commutes with all later symmetry breaking (permutations and variable
       negations fix n_empty), we may assume n_empty <= 0. */
    for (int c0 = 0; c0 >= -4; c0--) {
        if (catmode && c0 < 0) break;
        coef[0] = c0; used_total = c0 * c0;
        step(0);
    }
    coef[0] = 0; used_total = 0;
    double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (catmode) {
        fprintf(stderr, "catalogue K=%d M=%d: %lld canonical links, %lld link-leaves, %lld nodes, %lld canon-rejects, %.2fs\n",
                n - 1, MASSMAX, cand_links[0], links_done, nodes, canon_rejects, dt);
    } else {
        fprintf(stderr, "n=%d: solutions=%lld leaves=%lld links_done=%lld nodes=%lld canon_rejects=%lld time=%.2fs\n",
                n, solutions, leaves, links_done, nodes, canon_rejects, dt);
        fprintf(stderr, "accepted links per step:");
        for (int v = 0; v < n; v++) fprintf(stderr, " %lld", cand_links[v]);
        fprintf(stderr, "\n");
    }
    return 0;
}
