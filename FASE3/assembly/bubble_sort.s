    li sp 1000
    mv x6 sp # Final array element

    #Add values to array
    li x10 1
    #Push to stack
    sw x10 0(sp)
    addi sp sp -4 

    li x10 22
    #Push to stack
    sw x10 0(sp)
    addi sp sp -4

    li x10 3
    #Push to stack
    sw x10 0(sp)
    addi sp sp -4

    li x10 42
    #Push to stack
    sw x10 0(sp)
    addi sp sp -4

    li x10 5
    #Push to stack
    sw x10 0(sp)
    addi sp sp -4

    li x10 62
    #Push to stack
    sw x10 0(sp)
    addi sp sp -4

    li x7 0 # didntSwap (bool)
    li x8 1 # Constant = 1

    WhileLoop:
        beq x7 x8 End # If you didnt swap, then the array is sorted
        mv x28 sp # i = sp
        addi x28 x28 4 # Primer elemento del array
        li x7 1 # didntSwap = true
        ForLoop:
            bge x28 x6 EndFor # If i >= sp, then end for loop
            lw x10 0(x28) # x10 = array[i]
            addi x28 x28 4 # i++
            lw x11 0(x28) # x11 = array[i]
            addi x28 x28 -4 # i--

            ble x10 x11 NotSwap # If x10 <= x11, then dont swap
            li x7 0 # didntSwap = false

            #Swap x10 and x11
            mv x12 x10
            mv x10 x11 
            mv x11 x12 
            
            sw x10 0(x28) # array[i] = x10
            addi x28 x28 4 # i++
            sw x11 0(x28) # array[i] = x11
            addi x28 x28 -4 # i--
            NotSwap:
                addi x28 x28 4 # i++
                beq x0 x0 ForLoop # Go to for loop
        EndFor:
            beq x0 x0 WhileLoop # Go to while loop
    End: 