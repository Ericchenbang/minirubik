# IDA* solver for the 2x2x2 cube, hand-written RV32I (optimized).
#
# Main ideas versus the first version
#   * Search cursor (face, turn) and the current child live in REGISTERS.
#     Memory is only touched when a node is pushed or popped.
#   * Face is represented by its table base pointers (pb, ob), not by an index,
#     so no per-child "which face" branching or multiply.
#   * "cost <= bound" becomes "h <= slack" (slack = bound - g), and the next
#     bound is tracked as the smallest excess e = h - slack (no g needed).
#   * Solution moves are NOT written in the hot path; each frame records the
#     move that led to it and the verifier replays from the frames.
#   * Length = bound - slack (no division by the frame size).
#   * Rank computation has no multiply chain: add the weight (720,120,24,6,2,1)
#     directly for each inversion.
#
# Assumption: orientation[] directly follows permutation[] in memory
# (permutation + 3*10080 == orientation), so s6 doubles as the end sentinel.
#
# Frame, 24 bytes, frame d at sp + 24*d  (13 frames + c[7] = 320 bytes)
#    0 u16 p            2 u16 o
#    4 u32 pb  (cursor: perm base of the face being tried)
#    8 u32 ob  (cursor: orientation base of that face)
#   12 u32 lpb (perm base of the move that created this node; -1 at root)
#   16 u32 lob (orientation base of that move)
#   20 u8  t   (cursor: next quarter-turn count, 1..3)
#   21 u8  lt  (quarter turns of the move that created this node)
#
# Registers in the search
#   s0 slack = bound - g        s1 fp (current frame)   s2 min excess
#   s3 &permutation_distance    s4 &orientation_distance
#   s5 &permutation             s6 &orientation (= end of permutation)
#   s8 10080 (perm face stride) s9 1458 (ori face stride)
#   s10 lpb (face of last move) s11 bound
#   t6 = 4 constant
#   a2 pb   a3 ob   a4 t   a5 cp   a6 co   a7 child frame ptr

    .text
_start:
    addi sp, sp, -320

# ------------------------------------------------------------ parse_state
    la   t0, state_str
    addi t1, sp, 312            # &c[0]
    mv   t3, t0
    addi t6, t0, 7              # end of the cubie ids
    li   t2, 0                  # seen mask
    li   t5, 7
cubie_loop:
    lbu  t4, 0(t3)
    addi t4, t4, -49            # '1'
    bgeu t4, t5, bad_input
    li   a2, 1
    sll  a2, a2, t4
    and  a3, t2, a2
    bnez a3, bad_input          # duplicate cubie
    or   t2, t2, a2
    sb   t4, 0(t1)
    addi t1, t1, 1
    addi t3, t3, 1
    bne  t3, t6, cubie_loop

    addi t6, t3, 7              # end of twists (t3 already at s+7)
    li   a1, 0                  # o
    li   t2, 0                  # twist sum
    li   a2, 0                  # previous digit
    li   t5, 3
twist_loop:
    lbu  t4, 0(t3)
    addi t4, t4, -49
    bgeu t4, t5, bad_input
    add  t2, t2, t4
    slli a3, a1, 1
    add  a1, a1, a3
    add  a1, a1, a2             # o = 3*o + previous digit (7th digit excluded)
    mv   a2, t4
    addi t3, t3, 1
    bne  t3, t6, twist_loop
mod3:
    bltu t2, t5, mod3_done
    addi t2, t2, -3
    j    mod3
mod3_done:
    bnez t2, bad_input
    lbu  t4, 0(t3)
    bnez t4, bad_input          # must end after 14 characters

    li   a0, 0                  # p
    addi t1, sp, 312
    addi t6, t1, 7              # end of c[]
    addi a3, t1, 6              # outer loop stops after i = 5
    la   t5, weights
rank_outer:
    lbu  t3, 0(t1)              # c[i]
    lhu  t4, 0(t5)              # weight of position i
    addi t2, t1, 1
rank_inner:
    lbu  a2, 0(t2)
    bgeu a2, t3, rank_skip
    add  a0, a0, t4             # one inversion: add its weight
rank_skip:
    addi t2, t2, 1
    bne  t2, t6, rank_inner
    addi t1, t1, 1
    addi t5, t5, 2
    bne  t1, a3, rank_outer

# ---------------------------------------------------------------- ida_star
    sh   a0, 0(sp)
    sh   a1, 2(sp)
    or   t0, a0, a1
    beqz t0, search_done        # already solved, a0 = 0

    la   s3, permutation_distance
    la   s4, orientation_distance
    la   s5, permutation
    la   s6, orientation        # == end of permutation[]
    li   s8, 10080
    li   s9, 1458
    li   t6, 4

    add  t0, s3, a0
    lbu  t0, 0(t0)
    add  t1, s4, a1
    lbu  t1, 0(t1)
    bgeu t0, t1, 1f
    mv   t0, t1
1:  mv   s2, t0                 # first iteration: bound = 0 + h(root)
    li   s11, 0

iter_done:                      # bound += smallest excess seen
    add  s11, s11, s2
    li   s2, 255
    addi s0, s11, -1            # slack at depth 0 children (g = 1)
    mv   s1, sp
    li   s10, -1
    sw   s10, 12(sp)
    mv   a2, s5
    mv   a3, s6
    li   a4, 1
    j    fs_check

next_face:
    add  a2, a2, s8
    add  a3, a3, s9
    li   a4, 1
fs_check:
    beq  a2, s6, pop            # all three faces tried
    beq  a2, s10, next_face     # same face as the previous move
    lhu  a5, 0(s1)              # child starts as the node itself
    lhu  a6, 2(s1)

gen:                            # apply one quarter turn of face (a2,a3)
    slli t0, a5, 1
    add  t0, t0, a2
    lhu  a5, 0(t0)              # p'
    slli t1, a6, 1
    add  t1, t1, a3
    lhu  a6, 0(t1)              # o'
    add  t0, s3, a5
    lbu  t0, 0(t0)              # hp
    add  t1, s4, a6
    lbu  t1, 0(t1)              # ho
    bgeu t0, t1, 2f
    mv   t0, t1                 # t0 = h
2:  sub  t1, t0, s0             # e = h - slack
    blez t1, pass               # cost <= bound
    bge  t1, s2, 3f
    mv   s2, t1                 # min excess -> next bound
3:  addi a4, a4, 1
    bne  a4, t6, gen
    j    next_face

pass:                           # t0 = h
    addi a7, s1, 24             # child frame
    sw   a2, 12(a7)             # record the move that creates it
    sw   a3, 16(a7)
    sb   a4, 21(a7)
    beqz t0, found
    sh   a5, 0(a7)
    sh   a6, 2(a7)
    mv   s10, a2                # child's last face
    addi a4, a4, 1              # advance the parent's cursor
    bne  a4, t6, push_save
    add  a2, a2, s8
    add  a3, a3, s9
    li   a4, 1
push_save:
    sw   a2, 4(s1)
    sw   a3, 8(s1)
    sb   a4, 20(s1)
    mv   s1, a7
    addi s0, s0, -1
    mv   a2, s5
    mv   a3, s6
    li   a4, 1
    j    fs_check

pop:
    beq  s1, sp, iter_done
    addi s1, s1, -24
    addi s0, s0, 1
    lw   a2, 4(s1)
    lw   a3, 8(s1)
    lbu  a4, 20(s1)
    lw   s10, 12(s1)
    addi t0, a4, -1
    beqz t0, fs_check           # next face from the node itself
    lhu  a5, 24(s1)             # continue turning the child kept in d+1
    lhu  a6, 26(s1)
    j    gen

found:
    sub  a0, s11, s0            # length = g = bound - slack
search_done:

# --------------------------------------------------- path_reaches_solved
    lhu  t0, 0(sp)
    lhu  t1, 2(sp)
    beqz a0, verify_done
    mv   t2, a0
    addi t3, sp, 24
verify_loop:
    lw   a2, 12(t3)
    lw   a3, 16(t3)
    lbu  t4, 21(t3)
verify_turn:
    slli a4, t0, 1
    add  a4, a4, a2
    lhu  t0, 0(a4)
    slli a4, t1, 1
    add  a4, a4, a3
    lhu  t1, 0(a4)
    addi t4, t4, -1
    bnez t4, verify_turn
    addi t3, t3, 24
    addi t2, t2, -1
    bnez t2, verify_loop
verify_done:
    or   t0, t0, t1
    beqz t0, exit
    li   a0, 255                # bad path
exit:
    li   a7, 93
    ecall
bad_input:
    li   a0, 250
    j    exit

    .data
    .balign 2
weights:
    .half 720, 120, 24, 6, 2, 1