/* IDA* for the 2x2x2 cube, written to translate cleanly to RV32I.
 *
 * Target rules this file follows:
 *   - no '*', '/', '%' on anything but compile-time powers of two, so the
 *     compiler never needs __mulsi3, __divsi3, __udivsi3 or __umodsi3;
 *   - no libc, no heap, no recursion, no floating point;
 *   - every table is const data produced on the host (tables.h).
 * Host-only conveniences (printf, statistics) sit behind macros.
 */
#include <stdint.h>
#include "./table.h"

enum { NCUBIE = 7, MAXD = 11 };

/* Per-face base pointers: indexing permutation[face][p] directly would need
 * face * 5040 * 2, a multiply by a non-power-of-two. */
static const uint16_t *const perm_face[3] = {permutation[0], permutation[1],
                                             permutation[2]};
static const uint16_t *const ori_face[3] = {orientation[0], orientation[1],
                                            orientation[2]};

/* The answer: move i turns solution_face[i] by solution_turn[i] quarter
 * turns (1 = R, 2 = R2, 3 = R').  Kept as two small arrays so the program
 * never has to compute face * 3 + turn. */
uint8_t solution_face[MAXD], solution_turn[MAXD];

#ifdef SOLVER_STATS
uint64_t nodes_expanded, nodes_generated;
#define COUNT(x) (++(x))
#else
#define COUNT(x) ((void) 0)
#endif

static inline uint32_t heuristic(uint32_t p, uint32_t o)
{
    uint32_t hp = permutation_distance[p], ho = orientation_distance[o];
    return hp > ho ? hp : ho;
}

/* Returns the optimal length and fills solution_*[].  The state is the pair
 * (permutation rank, orientation rank); 0 is the solved cube, and
 * heuristic(p, o) == 0 holds only there, so h == 0 is the goal test.
 *
 * One explicit stack frame per depth:
 *   sp/so  state at that depth (slot d+1 also keeps the most recent child)
 *   face/turn  cursor over the children still to try (face 3 = exhausted)
 *   last   face of the move that produced this node (3 = none)
 */
uint32_t ida_star(uint32_t p0, uint32_t o0)
{
    uint16_t sp[MAXD + 2], so[MAXD + 2];
    uint8_t face[MAXD + 1], turn[MAXD + 1], last[MAXD + 1];

#ifdef SOLVER_STATS
    nodes_expanded = nodes_generated = 0;
#endif
    if (p0 == 0 && o0 == 0)
        return 0;

    uint32_t bound = heuristic(p0, o0);
    for (;;) {
        uint32_t next_bound = 0xff; /* smallest f that exceeded this bound */
        uint32_t d = 0;
        sp[0] = (uint16_t) p0;
        so[0] = (uint16_t) o0;
        face[0] = 0;
        turn[0] = 1;
        last[0] = 3;

        for (;;) {
            uint32_t f = face[d], t = turn[d];
            if (f == 3) { /* all children of this node tried */
                if (d == 0)
                    break;
                --d;
                continue;
            }
            if (f == last[d]) { /* same face twice is one move: skip it */
                face[d] = (uint8_t) (f + 1);
                turn[d] = 1;
                continue;
            }
            /* advance the cursor, then generate that child */
            if (t == 3) {
                face[d] = (uint8_t) (f + 1);
                turn[d] = 1;
            } else {
                turn[d] = (uint8_t) (t + 1);
            }
            /* turn 1 starts from this node; turn 2 and 3 take one more
             * quarter turn from the child just generated (kept in d+1). */
            uint32_t src = d + (t > 1);
            uint32_t p = perm_face[f][sp[src]], o = ori_face[f][so[src]];
            uint32_t g = d + 1, h = heuristic(p, o), cost = g + h;
            sp[g] = (uint16_t) p;
            so[g] = (uint16_t) o;
            COUNT(nodes_generated);
            if (cost > bound) {
                if (cost < next_bound)
                    next_bound = cost;
                continue;
            }
            solution_face[d] = (uint8_t) f;
            solution_turn[d] = (uint8_t) t;
            if (h == 0)
                return g;
            COUNT(nodes_expanded);
            face[g] = 0;
            turn[g] = 1;
            last[g] = (uint8_t) f;
            d = g;
        }
        bound = next_bound;
    }
}

/* ---- input: 14 characters, 7 cubie ids then 7 twists, each '1'-based ---- */

static inline uint32_t times3(uint32_t x) { return (x << 1) + x; }
static inline uint32_t times5(uint32_t x) { return (x << 2) + x; }
static inline uint32_t times6(uint32_t x) { return (x << 2) + (x << 1); }

/* (a + b) mod 3 for a, b <= 2 with no divide: subtract 3 once if the result
 * is not already below 3; the sign of (sum - 3) selects it. */
static inline uint32_t add_mod3(uint32_t a, uint32_t b)
{
    // int32_t t = (int32_t) (a + b) - 3;
    // return (uint32_t) (t + (3 & (t >> 31)));
    uint32_t t = a + b;
    if (t >= 3)
        t-= 3;
    return t;
}

static inline uint32_t smaller_after(const uint32_t *c, uint32_t i)
{
    uint32_t n = 0;
    for (uint32_t j = i + 1; j < NCUBIE; ++j)
        n += c[j] < c[i];
    return n;
}

/* Returns 1 and writes the two ranks if the string is a legal state, else 0.
 * Rank formulas match rank_state() of the C baseline, with the multiplies
 * by 6, 5, 4, 3, 2 and 3 written as shifts and adds. */
int parse_state(const char *s, uint32_t *p_out, uint32_t *o_out)
{
    uint32_t c[NCUBIE], seen = 0, o = 0, twist_sum = 0;

    for (uint32_t i = 0; i < NCUBIE; ++i) {
        uint32_t v = (uint32_t) (uint8_t) s[i] - '1';
        if (v >= NCUBIE || (seen >> v & 1))
            return 0;
        seen |= 1u << v;
        c[i] = v;
    }
    for (uint32_t i = 0; i < NCUBIE; ++i) {
        uint32_t v = (uint32_t) (uint8_t) s[NCUBIE + i] - '1';
        if (v >= 3)
            return 0;
        twist_sum = add_mod3(twist_sum, v);
        if (i < NCUBIE - 1)
            o = times3(o) + v; /* last twist is implied by the others */
    }
    if (twist_sum != 0 || s[2 * NCUBIE] != '\0')
        return 0;

    uint32_t p = smaller_after(c, 0);
    p = times6(p) + smaller_after(c, 1);
    p = times5(p) + smaller_after(c, 2);
    p = (p << 2) + smaller_after(c, 3);
    p = times3(p) + smaller_after(c, 4);
    p = (p << 1) + smaller_after(c, 5);
    *p_out = p;
    *o_out = o;
    return 1;
}

/* T5 inside the program: replay the answer with the same transition tables
 * and confirm it ends at the solved state. */
int path_reaches_solved(uint32_t p, uint32_t o, uint32_t length)
{
    for (uint32_t i = 0; i < length; ++i)
        for (uint32_t k = 0; k < solution_turn[i]; ++k) {
            p = perm_face[solution_face[i]][p];
            o = ori_face[solution_face[i]][o];
        }
    return p == 0 && o == 0;
}

/* Solve a state string.  Returns the number of moves, or -1 if illegal. */
int solve(const char *state)
{
    uint32_t p, o;
    if (!parse_state(state, &p, &o))
        return -1;
    return (int) ida_star(p, o);
}

#ifdef SOLVER_HOST_MAIN
#include <stdio.h>
int main(int argc, char **argv)
{
    static const char *const names[3][3] = {
        {"R", "R2", "R'"}, {"B", "B2", "B'"}, {"D", "D2", "D'"}};
    if (argc != 2) {
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n", argv[0]);
        return 2;
    }
    int len = solve(argv[1]);
    if (len < 0) {
        fputs("illegal state\n", stderr);
        return 2;
    }
    for (int i = 0; i < len; ++i)
        printf("%s%s", i ? " " : "",
               names[solution_face[i]][solution_turn[i] - 1]);
    putchar('\n');
#ifdef SOLVER_STATS
    fprintf(stderr, "length %d, expanded %llu, generated %llu\n", len,
            (unsigned long long) nodes_expanded,
            (unsigned long long) nodes_generated);
#endif
    return 0;
}
#endif