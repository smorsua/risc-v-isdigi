li x10, 100 # N = 100
 
li x11, 0 # f1 = 0
 
li x12, 1 # f2 = 1
 
li x13, 1 # Counter. i = 1 porque voy a guardar el primer termino antes del bucle y para hacer 19 más iteraciones empiezo en 1 (<=)
 
li sp 1000
 
sw x12 0(sp) # Guardo el primer término
 
addi sp, sp, -4
 
Loop:
	bge x13, x10, Done
    nop 
    nop
    nop
    nop 
    nop 
    mv x14, x12 # Guardo x12 en x14   
    add x12, x11, x12 # Guardo en x12 el nuevo término
	mv x11, x14 # Guardo en x11 el antiguo x12   
	sw x12 0(sp) # Guardo el n-ésimo término   
	addi sp, sp, -4   
    addi x13, x13, 1
    beq x0 x0 Loop
    nop
    nop
    nop
    nop
    nop
Done: