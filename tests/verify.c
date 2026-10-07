/* Host-side correctness gates for the IDA* solver (never built for the target).
 *
 *   cc -O2 -std=c99 -Wall -Wextra tests/verify.c -o verify
 *   ./verify tables          C0 factored tables == apply_move/rank_state
 *   ./verify dist            C1 BFS level counts == published distribution
 *   ./verify h1              H1 h(s) <= d(s) for every state
 *   ./verify h2              H2 PDBs fully populated, solved entry 0
 *   ./verify h3 [MOD [REM]]  H3 optimal length + path solves, states r with
 *                            r % MOD == REM (MOD=1: all; split across cores)
 *   ./verify all             tables, dist, h1, h2, then h3 over everything
 */
#define SOLVER_NO_MAIN 1
#include "../ida_solver.c"
#include <time.h>

static uint8_t exact_distance[STATES];

/* Oracle: plain BFS over the factored tables (same as the C baseline). */
static void build_exact_distance(void)
{
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint32_t head = 0, tail = 0;
    if (!queue) {
        fputs("cannot allocate BFS queue\n", stderr);
        exit(1);
    }
    memset(exact_distance, 0xff, sizeof exact_distance);
    exact_distance[0] = 0;
    queue[tail++] = 0;
    while (head < tail) {
        uint32_t s = queue[head++];
        uint16_t p = (uint16_t) (s / ORIENTATIONS), o = s % ORIENTATIONS;
        uint8_t d = exact_distance[s];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t np = p, no = o;
            for (uint8_t turns = 1; turns <= 3; ++turns) {
                np = permutation[face][np];
                no = orientation[face][no];
                uint32_t next = (uint32_t) np * ORIENTATIONS + no;
                if (exact_distance[next] == 0xff) {
                    exact_distance[next] = (uint8_t) (d + 1);
                    queue[tail++] = next;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        fprintf(stderr, "BFS visited %u / %u states\n", tail, STATES);
        exit(1);
    }
}

/* C0: the BFS above and the search both trust permutation[][] and
 * orientation[][].  Check them against the independent model
 * (unrank -> apply_move -> rank) for every state and every move. */
static int check_tables(void)
{
    uint32_t bad = 0;
    for (uint32_t r = 0; r < STATES; ++r) {
        state_t s;
        unrank_state(r, &s);
        for (uint8_t m = 0; m < MOVES; ++m) {
            uint8_t face = m / 3, turns = m % 3 + 1;
            uint16_t p = (uint16_t) (r / ORIENTATIONS), o = r % ORIENTATIONS;
            for (uint8_t k = 0; k < turns; ++k) {
                p = permutation[face][p];
                o = orientation[face][o];
            }
            state_t t = apply_move(s, m);
            if (rank_state(&t) != (uint32_t) p * ORIENTATIONS + o && bad++ < 5)
                printf("C0 mismatch: rank %u move %u\n", r, m);
        }
    }
    printf("C0: transition-table mismatches = %u\n", bad);
    return bad == 0;
}

/* C1: level sizes of the HTM Cayley graph (Scherphuis, Pocket Cube). */
static int check_distribution(void)
{
    static const uint32_t known[12] = {1,     9,      54,      321,
                                       1847,  9992,   50136,   227536,
                                       870072, 1887748, 623800, 2644};
    uint32_t count[256] = {0};
    int ok = 1;
    for (uint32_t r = 0; r < STATES; ++r)
        ++count[exact_distance[r]];
    for (int d = 0; d < 12; ++d) {
        printf("  d=%2d: %8u%s\n", d, count[d],
               count[d] == known[d] ? "" : "   <-- MISMATCH");
        ok &= count[d] == known[d];
    }
    printf("C1: distribution %s, diameter 11\n", ok ? "matches" : "DIFFERS");
    return ok;
}

static int verify_heuristic_admissibility(void)
{
    uint32_t violations = 0, slack[12] = {0};
    uint8_t max_h = 0;
    for (uint32_t s = 0; s < STATES; ++s) {
        uint8_t h = heuristic((uint16_t) (s / ORIENTATIONS), s % ORIENTATIONS);
        uint8_t d = exact_distance[s];
        if (h > max_h)
            max_h = h;
        if (h > d) {
            if (violations < 10)
                printf("H1 violation: state=%u, h=%u, d=%u\n", s, h, d);
            ++violations;
        } else {
            ++slack[d - h];
        }
    }
    printf("H1: max h = %u, violations = %u; slack d-h histogram:", max_h,
           violations);
    for (int i = 0; i < 12; ++i)
        printf(" %u", slack[i]);
    putchar('\n');
    return violations == 0;
}

static int verify_pdb(void)
{
    uint8_t pmax = 0, omax = 0;
    for (uint16_t i = 0; i < PERMUTATIONS; ++i) {
        if (permutation_distance[i] == 0xff)
            return printf("H2: permutation entry %u unpopulated\n", i), 0;
        if (permutation_distance[i] > pmax)
            pmax = permutation_distance[i];
    }
    for (uint16_t i = 0; i < ORIENTATIONS; ++i) {
        if (orientation_distance[i] == 0xff)
            return printf("H2: orientation entry %u unpopulated\n", i), 0;
        if (orientation_distance[i] > omax)
            omax = orientation_distance[i];
    }
    printf("H2: permutation PDB max %u solved %u; orientation PDB max %u "
           "solved %u\n", pmax, permutation_distance[0], omax,
           orientation_distance[0]);
    return permutation_distance[0] == 0 && orientation_distance[0] == 0;
}

/* Replay the path with apply_move, not with the tables the search used. */
static int path_solves(uint32_t rank, uint8_t length)
{
    state_t s;
    unrank_state(rank, &s);
    for (uint8_t i = 0; i < length; ++i)
        s = apply_move(s, solution[i]);
    return rank_state(&s) == 0;
}

static void state_string(uint32_t rank, char out[15])
{
    state_t s;
    unrank_state(rank, &s);
    for (uint8_t i = 0; i < CUBIES; ++i) {
        out[i] = (char) ('1' + s.p[i]);
        out[i + CUBIES] = (char) ('1' + s.o[i]);
    }
    out[14] = '\0';
}

static int verify_ida_optimality(uint32_t mod, uint32_t rem)
{
    uint32_t failures = 0;
    uint64_t count = 0, total = 0, max_exp = 0, max_gen = 0, max11 = 0;
    uint32_t worst11 = 0;
    time_t t0 = time(NULL);
    for (uint32_t r = rem; r < STATES; r += mod) {
        uint8_t expected = exact_distance[r];
        uint8_t actual = ida_star((uint16_t) (r / ORIENTATIONS),
                                  r % ORIENTATIONS);
        if (actual != expected || !path_solves(r, actual)) {
            if (failures++ < 10)
                printf("H3 failure: state=%u, expected=%u, actual=%u\n", r,
                       expected, actual);
        }
        ++count;
        total += nodes_expanded;
        if (nodes_expanded > max_exp)
            max_exp = nodes_expanded;
        if (nodes_generated > max_gen)
            max_gen = nodes_generated;
        if (expected == 11 && nodes_expanded > max11) {
            max11 = nodes_expanded;
            worst11 = r;
        }
    }
    char text[15] = "";
    if (max11)
        state_string(worst11, text);
    printf("H3: %llu states (r %% %u == %u), failures = %u, wall %lds\n",
           (unsigned long long) count, mod, rem, failures,
           (long) (time(NULL) - t0));
    printf("    expanded: mean %.1f, max %llu; generated max %llu; "
           "d=11 worst expanded %llu at %s\n",
           count ? (double) total / (double) count : 0.0,
           (unsigned long long) max_exp, (unsigned long long) max_gen,
           (unsigned long long) max11, text);
    return failures == 0;
}

int main(int argc, char **argv)
{
    const char *cmd = argc > 1 ? argv[1] : "all";
    uint32_t mod = argc > 2 ? (uint32_t) atoi(argv[2]) : 1;
    uint32_t rem = argc > 3 ? (uint32_t) atoi(argv[3]) : 0;
    int all = !strcmp(cmd, "all"), ok = 1, ran = 0;

    if (mod == 0 || rem >= mod) {
        fputs("need MOD >= 1 and REM < MOD\n", stderr);
        return 2;
    }
    build_transition_tables();
    build_permutation_pdb();
    build_orientation_pdb();

    if (all || !strcmp(cmd, "tables")) { ok &= check_tables(); ran = 1; }
    build_exact_distance();
    if (all || !strcmp(cmd, "dist"))   { ok &= check_distribution(); ran = 1; }
    if (all || !strcmp(cmd, "h1"))     { ok &= verify_heuristic_admissibility(); ran = 1; }
    if (all || !strcmp(cmd, "h2"))     { ok &= verify_pdb(); ran = 1; }
    if (all || !strcmp(cmd, "h3"))     { ok &= verify_ida_optimality(mod, rem); ran = 1; }
    if (!ran) {
        fprintf(stderr, "usage: %s tables|dist|h1|h2|h3 [MOD [REM]]|all\n", argv[0]);
        return 2;
    }
    puts(ok ? "ALL REQUESTED CHECKS PASSED" : "SOME CHECK FAILED");
    return !ok;
}