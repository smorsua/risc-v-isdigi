addi x10, x0, 100 # N = 100
addi x11, x0, 0 # f1 = 0
addi x12, x0, 1 # f2 = 1
addi x13, x0, 1 # i = 1 porque voy a guardar el primer termino antes del bucle y para hacer 19 más iteraciones empiezo en 1 (<=)

sw x12 0(sp) # Guardo el primer término
addi sp, sp, -4
Loop:
	bge x13, x10, Done
    add x14, x12, x0 # Guardo x12 en x14
    add x12, x11, x12 # Guardo en x12 el nuevo término
	add x11, x14, x0 # Guardo en x11 el antiguo x12
	sw x12 0(sp) # Guardo el n-ésimo término
	addi sp, sp, -4
    addi x13, x13, 1
    j Loop
    
Done: