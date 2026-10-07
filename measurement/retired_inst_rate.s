.text
main:
    addi t0, t0, 0
    lui t1, 100

loop:
    addi t0, t0, 1
    bne t0, t1, loop

finish:
    addi a7, x0, 10        # halts the simulator execution
    ecall
