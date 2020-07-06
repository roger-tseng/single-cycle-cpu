.data
    n: .word 10 # You can change this number
    
.text
.globl __start

FUNCTION:
    addi x8, x10, 0
Loop:
    addi sp, sp, -16
    sw x1, 8(sp)
    sw x8, 0(sp)
    srli x28, x8, 1 # x28 = n/2
    addi x6, x0, 1  # set x6 to 1
    bge x28, x6, L1
    addi x10, x0, 1
    addi sp, sp, 16
    jalr x0, 0(x1)
    
L1:
    srli x8, x8, 1 # n' = n/2
    jal x1, Loop
    addi x6, x10, 0 # save result of T(n/2) to x6
    lw x8, 0(sp)
    lw x1, 8(sp)
    addi sp, sp, 16
    slli x10, x10, 2
    slli x29, x8, 1 # x29 = 2n
    add x10, x10, x29
    jalr x0, 0(x1)
    

# Do not modify this part!!! #
__start:                     #
    la   t0, n               #
    lw   x10, 0(t0)          #
    jal  x1,FUNCTION         #
    la   t0, n               #
    sw   x10, 4(t0)          #
    addi a0,x0,10            #
    ecall                    #
##############################