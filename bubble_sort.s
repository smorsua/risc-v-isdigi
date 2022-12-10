
mv x6 sp # Final array element

#Add values to array
li x10 1
sw x10 0(sp)
addi sp sp -4

li x10 2
sw x10 0(sp)
addi sp sp -4

li x10 3
sw x10 0(sp)
addi sp sp -4

li x10 4
sw x10 0(sp)
addi sp sp -4

li x10 5
sw x10 0(sp)
addi sp sp -4

li x10 6
sw x10 0(sp)
addi sp sp -4

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
        mv x12 x10
   		mv x10 x11
    	mv x11 x12
        sw x10 0(x28)
        addi x28 x28 4
        sw x11 0(x28)
        addi x28 x28 -4
        NotSwap:
            addi x28 x28 4
            beq x0 x0 ForLoop
    EndFor:
    	beq x0 x0 WhileLoop
End: