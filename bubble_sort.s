li sp 1000
mv x6 sp # Final array element

#Add values to array
li x10 1
#Push to stack
sw x10 0(sp)
addi sp sp -4

li x10 2
#Push to stack
sw x10 0(sp)
addi sp sp -4

li x10 3
#Push to stack
sw x10 0(sp)
addi sp sp -4

li x10 4
#Push to stack
sw x10 0(sp)
addi sp sp -4

li x10 5
#Push to stack
sw x10 0(sp)
addi sp sp -4

li x10 6
#Push to stack
sw x10 0(sp)
addi sp sp -4

li x7 0 # didntSwap (bool)
li x8 1 # Constant = 1

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
        #Swap x10 and x11
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