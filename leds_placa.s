addi x1, x0,0 #valor
addi x14, x0,14

loop: addi x1, x1,1
sw x1, 0(x1)
lui x2, 1
add x2,x2,x1
sw x1, 0(x2)
bne x14, x1, loop
end: