.text
main:
    lui t0, 0x10000
    lui t1, 0x100      # 64 KB = 0x10000, 1MB = 0x100000
    addi t1, t1, 0
    add t1, t0, t1
loop:
    sw x0, 0(t0)
    addi t0, t0, 4
    bne t1, t0, loop

finish:
    addi a7, x0, 10
    ecall

