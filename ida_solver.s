# IDA* solver for the 2x2x2 cube, hand-written RV32I.
#
# Program flow (no functions, no ABI: everything is one straight program):
#   1. parse the 14-character state string into (p, o) ranks
#   2. IDA* search -> length in a0, moves in solution_face/solution_turn
#   3. replay the moves with the same tables and check we reach "solved"
#   4. exit(code): length on success, 250 illegal input, 255 bad path
#
# Registers used by the search (same roles as in solver.c):
#   s0 bound        s1 d           s2 next_bound
#   s3 &sp[0]       s4 &so[0]      s5 &face[0]   s6 &turn[0]   s7 &last[0]
#   s8 permutation_distance  s9 orientation_distance
#   s10 permutation          s11 orientation
#   t2 f (face)     t3 t (turn)    t6 g = d + 1
#
# Frame (160 bytes, offsets from sp):
#     0  uint16 sp[13]          32  uint16 so[13]
#    64  uint8  face[12]        80  uint8  turn[12]     96  uint8 last[12]
#   112  uint8  solution_face[11]   128 uint8 solution_turn[11]
#   144  uint8  c[7]  (cubie ids while parsing)

    .text
_start:
    addi sp, sp, -160

# ------------------------------------------------------------ parse_state
    la   t0, state_str
    li   t1, 0                  # i
    li   t2, 0                  # seen mask
    li   t5, 7
cubie_loop:
    add  t3, t0, t1
    lbu  t3, 0(t3)
    addi t3, t3, -49            # '1'
    bgeu t3, t5, bad_input      # v >= 7 (unsigned also catches v < 0)
    li   t4, 1
    sll  t4, t4, t3
    and  t6, t2, t4
    bnez t6, bad_input          # duplicate cubie
    or   t2, t2, t4
    addi t6, sp, 144
    add  t6, t6, t1
    sb   t3, 0(t6)              # c[i] = v
    addi t1, t1, 1
    bne  t1, t5, cubie_loop

    li   a1, 0                  # o
    li   t2, 0                  # twist sum mod 3
    li   t1, 0                  # i
    li   t5, 3
    li   t6, 7
twist_loop:
    add  t3, t0, t1
    lbu  t3, 7(t3)
    addi t3, t3, -49
    bgeu t3, t5, bad_input      # twist must be 0..2
    add  t2, t2, t3
    blt  t2, t5, twist_nowrap
    addi t2, t2, -3             # (a + b) mod 3 for a, b <= 2
twist_nowrap:
    li   t4, 6
    bgeu t1, t4, twist_skip     # last twist is implied by the others
    slli t4, a1, 1
    add  a1, t4, a1             # o * 3
    add  a1, a1, t3
twist_skip:
    addi t1, t1, 1
    bne  t1, t6, twist_loop
    bnez t2, bad_input          # twist sum must be 0 mod 3
    lbu  t3, 14(t0)
    bnez t3, bad_input          # string must end after 14 characters

    li   a0, 0                  # p
    li   t1, 0                  # i
    addi t0, sp, 144            # &c[0]
rank_loop:
    add  t2, t0, t1
    lbu  t3, 0(t2)              # c[i]
    li   t4, 0                  # count of j > i with c[j] < c[i]
    addi t5, t1, 1              # j
    li   t6, 7
count_loop:
    bgeu t5, t6, count_done
    add  t2, t0, t5
    lbu  t2, 0(t2)
    sltu t2, t2, t3
    add  t4, t4, t2
    addi t5, t5, 1
    j    count_loop
count_done:
    li   t2, 7
    sub  t2, t2, t1             # radix r = 7 - i
    mv   t3, a0                 # old p
    li   a0, 0
mul_loop:                       # a0 = old p * r  (no mul in RV32I)
    beqz t2, mul_done
    add  a0, a0, t3
    addi t2, t2, -1
    j    mul_loop
mul_done:
    add  a0, a0, t4             # p = p * r + count
    addi t1, t1, 1
    li   t2, 6
    bne  t1, t2, rank_loop      # i = 0 .. 5

# ---------------------------------------------------------------- ida_star
    mv   s3, sp                 # sp[]
    addi s4, sp, 32             # so[]
    addi s5, sp, 64             # face[]
    addi s6, sp, 80             # turn[]
    addi s7, sp, 96             # last[]
    la   s8, permutation_distance
    la   s9, orientation_distance
    la   s10, permutation
    la   s11, orientation

    sh   a0, 0(s3)              # sp[0] = p0
    sh   a1, 0(s4)              # so[0] = o0
    or   t0, a0, a1
    beqz t0, search_done        # already solved: a0 = 0 moves

    add  t0, s8, a0
    lbu  t0, 0(t0)              # hp
    add  t1, s9, a1
    lbu  t1, 0(t1)              # ho
    bgeu t0, t1, root_h
    mv   t0, t1
root_h:
    mv   s0, t0                 # bound = h(root)

first_for_loop:
    li   s2, 255                # next_bound
    li   s1, 0                  # d
    sb   x0, 0(s5)              # face[0] = 0
    li   t0, 1
    sb   t0, 0(s6)              # turn[0] = 1
    li   t0, 3
    sb   t0, 0(s7)              # last[0] = 3 (no face)

second_for_loop:
    add  t0, s1, s5
    add  t1, s1, s6
    lbu  t2, 0(t0)              # f = face[d]
    lbu  t3, 0(t1)              # t = turn[d]
    li   t5, 3
    bne  t2, t5, check_last
    beqz s1, exit_second_for_loop
    addi s1, s1, -1             # all faces tried: backtrack
    j    second_for_loop
check_last:
    add  t0, s1, s7
    lbu  t4, 0(t0)              # last[d]
    bne  t2, t4, check_turn
    addi t0, t2, 1              # same face as the previous move: skip it
    add  t1, s1, s5
    sb   t0, 0(t1)              # face[d] = f + 1
    li   t0, 1
    add  t1, s1, s6
    sb   t0, 0(t1)              # turn[d] = 1
    j    second_for_loop
check_turn:
    li   t0, 3
    bne  t3, t0, turn_plus_one
    addi t0, t2, 1
    add  t1, s1, s5
    sb   t0, 0(t1)              # face[d] = f + 1
    li   t0, 1
    add  t1, s1, s6
    sb   t0, 0(t1)              # turn[d] = 1
    j    find_src
turn_plus_one:
    addi t0, t3, 1
    add  t1, s1, s6
    sb   t0, 0(t1)              # turn[d] = t + 1
find_src:
    mv   t6, s1                 # src = d
    li   t0, 2
    bltu t3, t0, next_p
    addi t6, t6, 1              # turn 2 and 3 continue from the last child
next_p:
    li   t5, 0                  # byte offset of this face in permutation[]
    beqz t2, find_p
    li   t5, 10080
    li   t0, 1
    beq  t2, t0, find_p
    li   t5, 20160
find_p:
    slli t6, t6, 1              # src * 2 (uint16_t)
    add  t0, t6, s3
    lhu  t4, 0(t0)              # sp[src]
    slli t4, t4, 1
    add  t4, t4, t5
    add  t4, s10, t4
    lhu  t4, 0(t4)              # p = permutation[f][sp[src]]
next_o:
    li   t5, 0                  # byte offset of this face in orientation[]
    beqz t2, find_o
    li   t5, 1458
    li   t0, 1
    beq  t2, t0, find_o
    li   t5, 2916
find_o:
    add  t0, t6, s4
    lhu  t1, 0(t0)              # so[src]
    slli t1, t1, 1
    add  t1, t1, t5
    add  t1, s11, t1
    lhu  t1, 0(t1)              # o = orientation[f][so[src]]

    addi t6, s1, 1              # g = d + 1
    slli t5, t6, 1
    add  t0, s3, t5
    sh   t4, 0(t0)              # sp[g] = p
    add  t0, s4, t5
    sh   t1, 0(t0)              # so[g] = o

    add  t0, s8, t4
    lbu  t0, 0(t0)              # hp
    add  t5, s9, t1
    lbu  t5, 0(t5)              # ho
    bgeu t0, t5, h_done
    mv   t0, t5
h_done:                         # t0 = h = max(hp, ho)
    add  t5, t0, t6             # cost = g + h
    bge  s0, t5, pass_bound     # cost <= bound
    bge  t5, s2, second_for_loop
    mv   s2, t5                 # next_bound = min(next_bound, cost)
    j    second_for_loop

pass_bound:
    addi t4, sp, 112
    add  t4, t4, s1
    sb   t2, 0(t4)              # solution_face[d] = f
    addi t4, sp, 128
    add  t4, t4, s1
    sb   t3, 0(t4)              # solution_turn[d] = t
    beqz t0, found              # h == 0: solved
    mv   s1, t6                 # d = g
    add  t4, s5, t6
    sb   x0, 0(t4)              # face[g] = 0
    add  t4, s6, t6
    li   t5, 1
    sb   t5, 0(t4)              # turn[g] = 1
    add  t4, s7, t6
    sb   t2, 0(t4)              # last[g] = f
    j    second_for_loop

exit_second_for_loop:
    mv   s0, s2                 # bound = next_bound
    j    first_for_loop

found:
    mv   a0, t6                 # length = g
search_done:

# --------------------------------------------------- path_reaches_solved
    lhu  t0, 0(s3)              # p = sp[0]
    lhu  t1, 0(s4)              # o = so[0]
    li   t3, 0                  # i
verify_loop:
    bgeu t3, a0, verify_done
    addi t4, sp, 112
    add  t4, t4, t3
    lbu  t4, 0(t4)              # face
    addi t5, sp, 128
    add  t5, t5, t3
    lbu  t5, 0(t5)              # number of quarter turns
    mv   a2, s10
    mv   a3, s11
    beqz t4, face_ok
    la   a2, permutation_f1
    la   a3, orientation_f1
    li   a4, 1
    beq  t4, a4, face_ok
    la   a2, permutation_f2
    la   a3, orientation_f2
face_ok:
turn_loop:
    slli a4, t0, 1
    add  a4, a2, a4
    lhu  t0, 0(a4)              # p = permutation[face][p]
    slli a4, t1, 1
    add  a4, a3, a4
    lhu  t1, 0(a4)              # o = orientation[face][o]
    addi t5, t5, -1
    bnez t5, turn_loop
    addi t3, t3, 1
    j    verify_loop
verify_done:
    or   t0, t0, t1
    bnez t0, bad_path
    j    exit                   # a0 = length
bad_path:
    li   a0, 255
    j    exit
bad_input:
    li   a0, 250
exit:
    li   a7, 93
    ecall