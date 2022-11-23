
mv x6 sp # Final array element

#Add values to array
li x10 1
jal x1 Push

li x10 2
jal x1 Push

li x10 3
jal x1 Push

li x10 4
jal x1 Push

li x10 5
jal x1 Push

li x10 6
jal x1 Push

li x7 0 # didntSwap (bool)
li x8 1 # Constant = 1
mv x13 sp
neg x13 x13
add x9 x6 x13 # Array length

WhileLoop:
    beq x7 x8 End
    mv x28 sp # i = sp
    addi x28 x28 4 # Primer elemento del array
     li x7 1
    ForLoop:
    bge x28 x6 EndFor

    lw x10 0(x28)
    addi x28 x28 4
    lw x11 0(x28)
    addi x28 x28 -4

    ble x10 x11 NotSwap
    li x7 0
    jal x1 Swap
    sw x10 0(x28)
    addi x28 x28 4
    sw x11 0(x28)
    addi x28 x28 -4
NotSwap:
    addi x28 x28 4
    j ForLoop
    EndFor:
    j WhileLoop

Swap: # Swap x10 and x11
    mv x12 x10
    mv x10 x11
    mv x11 x12
    jalr x0 x1 0

Push: #push x10 to stack
    sw x10 0(sp)
    addi sp sp -4
    jalr x0 x1 0

End: