#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9,
    MAX_DEPTH = 11
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}


/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    return 1;
}

static uint16_t permutation[3][PERMUTATIONS];
static uint16_t orientation[3][ORIENTATIONS];

static void build_transition_tables()
{
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        state_t state = {0};
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        state_t state = {0};
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
}


static uint8_t permutation_distance[PERMUTATIONS];
static uint8_t orientation_distance[ORIENTATIONS];

static void build_permutation_pdb(void)
{
    uint16_t queue[PERMUTATIONS];

    memset(permutation_distance, 0xff,
           sizeof(permutation_distance));

    uint16_t head = 0;
    uint16_t tail = 0;

    permutation_distance[0] = 0;
    queue[tail++] = 0;

    while (head < tail) {
        uint16_t p = queue[head++];
        uint8_t distance = permutation_distance[p];

        for (uint8_t face = 0; face < 3; ++face) {

            // quarter turn: R / B / D 
            uint16_t next =
                permutation[face][p];

            if (permutation_distance[next] == 0xff) {
                permutation_distance[next] =
                    distance + 1;
                queue[tail++] = next;
            }

            // half turn: R2 / B2 / D2 
            next = permutation[face][next];

            if (permutation_distance[next] == 0xff) {
                permutation_distance[next] =
                    distance + 1;
                queue[tail++] = next;
            }

            // inverse quarter turn: R' / B' / D' 
            next = permutation[face][next];

            if (permutation_distance[next] == 0xff) {
                permutation_distance[next] =
                    distance + 1;
                queue[tail++] = next;
            }
        }
    }
}

static void build_orientation_pdb(void)
{
    uint16_t queue[ORIENTATIONS];

    memset(orientation_distance, 0xff,
           sizeof(orientation_distance));

    uint16_t head = 0;
    uint16_t tail = 0;

    orientation_distance[0] = 0;
    queue[tail++] = 0;

    while (head < tail) {
        uint16_t o = queue[head++];
        uint8_t distance = orientation_distance[o];

        for (uint8_t face = 0; face < 3; ++face) {

            // R / B / D 
            uint16_t next =
                orientation[face][o];

            if (orientation_distance[next] == 0xff) {
                orientation_distance[next] =
                    distance + 1;
                queue[tail++] = next;
            }

            // R2 / B2 / D2 
            next = orientation[face][next];

            if (orientation_distance[next] == 0xff) {
                orientation_distance[next] =
                    distance + 1;
                queue[tail++] = next;
            }

            // R' / B' / D' 
            next = orientation[face][next];

            if (orientation_distance[next] == 0xff) {
                orientation_distance[next] =
                    distance + 1;
                queue[tail++] = next;
            }
        }
    }
}

static uint8_t heuristic(uint16_t p, uint16_t o)
{
    uint8_t hp = permutation_distance[p];
    uint8_t ho = orientation_distance[o];

    return hp > ho ? hp : ho;
}

// verify H1
static uint8_t exact_distance[STATES];
static void build_exact_distance(void)
{
    uint32_t *queue = malloc((size_t)STATES * sizeof(*queue));

    if (queue == NULL) {
        fprintf(stderr, "failed to allocate BFS queue\n");
        exit(EXIT_FAILURE);
    }

    for (uint32_t i = 0; i < STATES; ++i)
        exact_distance[i] = 0xff;

    uint32_t head = 0;
    uint32_t tail = 0;

    exact_distance[0] = 0;
    queue[tail++] = 0;

    while (head < tail) {
        uint32_t state = queue[head++];
        uint16_t p = state / ORIENTATIONS;
        uint16_t o = state % ORIENTATIONS;
        uint8_t d = exact_distance[state];

        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t np = permutation[face][p];
            uint16_t no = orientation[face][o];

            for (uint8_t turns = 1; turns <= 3; ++turns) {
                if (turns > 1) {
                    np = permutation[face][np];
                    no = orientation[face][no];
                }

                uint32_t next =
                    (uint32_t)np * ORIENTATIONS + no;

                if (exact_distance[next] == 0xff) {
                    exact_distance[next] = d + 1;
                    queue[tail++] = next;
                }
            }
        }
    }

    if (tail != STATES) {
        fprintf(stderr,
                "ERROR: BFS visited %u / %u states\n",
                tail, STATES);
        free(queue);
        exit(EXIT_FAILURE);
    }

    free(queue);
}

// verify H1
static int verify_heuristic_admissibility(void)
{
    uint32_t violations = 0;
    uint8_t max_h = 0;
    uint8_t max_d = 0;

    for (uint32_t state = 0; state < STATES; ++state) {
        uint16_t p = state / ORIENTATIONS;
        uint16_t o = state % ORIENTATIONS;

        uint8_t h = heuristic(p, o);
        uint8_t d = exact_distance[state];

        if (h > max_h)
            max_h = h;

        if (d > max_d)
            max_d = d;

        if (h > d) {
            if (violations < 10) {
                printf("H1 violation: state=%u, h=%u, d=%u\n",
                       state, h, d);
            }
            ++violations;
        }
    }

    printf("H1: max heuristic = %u\n", max_h);
    printf("H1: max exact distance = %u\n", max_d);
    printf("H1: violations = %u\n", violations);

    return violations == 0;
}


// verify H2
static int verify_pdb(void)
{
    uint8_t permutation_max = 0;
    uint8_t orientation_max = 0;

    for (uint16_t i = 0; i < PERMUTATIONS; ++i) {
        if (permutation_distance[i] == 0xff)
            return 0;

        if (permutation_distance[i] > permutation_max)
            permutation_max = permutation_distance[i];
    }

    for (uint16_t i = 0; i < ORIENTATIONS; ++i) {
        if (orientation_distance[i] == 0xff)
            return 0;

        if (orientation_distance[i] > orientation_max)
            orientation_max = orientation_distance[i];
    }

    if (permutation_distance[0] != 0)
        return 0;

    if (orientation_distance[0] != 0)
        return 0;

    printf("Permutation PDB: max = %u, solved = %u\n",
           permutation_max,
           permutation_distance[0]);

    printf("Orientation PDB: max = %u, solved = %u\n",
           orientation_max,
           orientation_distance[0]);

    return 1;
}

static uint8_t solution[MAX_DEPTH]; /* solution[i] = i-th move, 0..8 */
static uint64_t nodes_expanded;
 
/* Returns the optimal length; the moves are left in solution[]. */
static uint8_t ida_star(uint16_t p0, uint16_t o0)
{
    uint16_t sp[MAX_DEPTH + 1], so[MAX_DEPTH + 1]; /* state at each depth */
    uint8_t next[MAX_DEPTH + 1];                   /* next move to try there */
 
    nodes_expanded = 0;
    
    if (p0 == 0 && o0 == 0)
        return 0;
    
    uint8_t bound = heuristic(p0, o0);
    for (;;) {
        uint8_t next_bound = 0xff;

        int d = 0;
        sp[0] = p0;
        so[0] = o0;
        next[0] = 0;

        while (d >= 0) {
            if (next[d] == MOVES) { /* all children tried: backtrack */
                --d;
                continue;
            }

            uint8_t m = next[d]++, face = m / 3, turns = m % 3 + 1;
            
            if (d > 0 && face == solution[d - 1] / 3)
                continue; /* same face twice in a row is one move */
            
            uint16_t p = sp[d], o = so[d];
            
            for (uint8_t k = 0; k < turns; ++k) {
                p = permutation[face][p];
                o = orientation[face][o];
            }
            
            uint8_t g = (uint8_t) (d + 1);
            uint8_t h = heuristic(p, o);
            uint8_t f = g + h;

            if (f > bound){             /* f = g + h exceeds this iteration's bound */
                if (f < next_bound){
                    next_bound = f;
                }
                continue;
            }
                
            solution[d] = m;
            
            if (h == 0) /* h == 0 only for the solved state here */
                return g;
            
            ++nodes_expanded;
            sp[g] = p;
            so[g] = o;
            next[g] = 0;
            d = g;
        }

        bound = next_bound;
    }
}

// verify T5
static int verify_solution(uint16_t p0, uint16_t o0, uint8_t length)
{
    uint16_t p = p0;
    uint16_t o = o0;

    for (uint8_t d = 0; d < length; ++d) {
        uint8_t m = solution[d];
        uint8_t face = m / 3;
        uint8_t turns = m % 3 + 1;

        for (uint8_t k = 0; k < turns; ++k) {
            p = permutation[face][p];
            o = orientation[face][o];
        }
    }

    return p == 0 && o == 0;
}

// verify H3
static int verify_ida_optimality(void)
{
    uint32_t failures = 0;

    for (uint32_t state = 0; state < STATES; ++state) {
        uint16_t p = (uint16_t)(state / ORIENTATIONS);
        uint16_t o = (uint16_t)(state % ORIENTATIONS);

        uint8_t expected = exact_distance[state];
        uint8_t actual = ida_star(p, o);

        if (actual != expected ||
            !verify_solution(p, o, actual)) {

            if (failures < 10) {
                printf("H3 failure: state=%u, expected=%u, actual=%u\n",
                       state, expected, actual);
            }

            ++failures;
        }

        if ((state + 1) % 100000 == 0) {
            printf("H3 progress: %u / %u\n",
                   state + 1, STATES);
        }
    }

    printf("H3: failures = %u\n", failures);

    return failures == 0;
}

static void init_tables(void)
{
    build_transition_tables();
    build_permutation_pdb();
    build_orientation_pdb();

    build_exact_distance();

    // verify H1
    // if (!verify_heuristic_admissibility()){
    //     fputs("Heuristic verification failed\n", stderr);
    //     exit(1);
    // }
        
    // verify H2
    if (!verify_pdb()) {
        fputs("PDB verification failed\n", stderr);
        exit(1);
    }
}

int main(int argc, char **argv)
{
    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        puts("moves and rank/unrank consistent");
        return output_failed();
    }

    /*
     * Host-side H1/H2/H3 verification.
     * No input state is required.
     */
    init_tables();

    if (!verify_heuristic_admissibility()) {
        fputs("Heuristic verification failed\n", stderr);
        return 1;
    }

    if (!verify_ida_optimality()) {
        fputs("IDA* optimality verification failed\n", stderr);
        return 1;
    }

    puts("H1/H2/H3 verification passed");

    return output_failed();
}


// int main(int argc, char **argv)
// {
//     state_t state;
//     uint8_t diameter;

//     if (argc == 2 && !strcmp(argv[1], "--self-test")) {
//         if (!self_test()) {
//             fputs("self-test failed\n", stderr);
//             return 1;
//         }
//         puts("moves and rank/unrank consistent");
//         return output_failed();
//     }
//     if (argc != 2 || !parse_state(argv[1], &state)) {
//         // C99 5.1.2.2.1 lets argv[0] be null when argc is 0. 
//         fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
//                 argc > 0 && argv[0] ? argv[0] : "solver");
//         return 2;
//     }
    
//     init_tables();
//     uint32_t rank = rank_state(&state);
//     uint8_t len = ida_star((uint16_t) (rank / ORIENTATIONS),
//                            (uint16_t) (rank % ORIENTATIONS));
//     // verify T5
//     if (!verify_solution((uint16_t) (rank / ORIENTATIONS),
//                            (uint16_t) (rank % ORIENTATIONS), len)) {
//         fprintf(stderr, "ERROR: solution does not reach solved state\n");
//         return 1;
//     }
    
//     for (uint8_t i = 0; i < len; ++i)
//         printf("%s%s", i ? " " : "", move_names[solution[i]]);
//     putchar('\n');
//     if (getenv("SOLVER_STATS"))
//         fprintf(stderr, "length %u, expanded %llu\n", len,
//                 (unsigned long long) nodes_expanded);
    
//     return output_failed();
// }
