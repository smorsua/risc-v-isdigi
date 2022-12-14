
addi x10,x0,3
addi x11,x0,4
jal x1, Leaf 
Leaf:  addi sp, sp, -4
sw x8, 2(sp)
add x8, x10, x11 
lw x8, 2(sp) 
addi sp, sp, 4
jalr x0, 0(x1)