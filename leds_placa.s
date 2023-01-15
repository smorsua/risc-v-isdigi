addi x1, x0,0 #valor
addi x14, x0,14

loop: addi x1, x1,1
sw x1, 200(x1)
bne x14, x1, loop
end: