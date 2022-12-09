addi x3, x0, 14
li x1 13
li x2 777
sw x1 0(x2)
auipc x6, 3
bne x1, x2, End
addi x2, x1, 15
End:  addi x2, x1, 8