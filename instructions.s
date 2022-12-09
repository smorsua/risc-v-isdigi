addi x3, x0, 14
jal x1, End
li x1 13
li x2 777
sw x1 0(x2)
auipc x6, 3
bge x2, x1, End
addi x2, x1, 15
End:  addi x2, x1, 3