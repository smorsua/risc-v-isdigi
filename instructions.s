li x1 40
li x2 40
beq x1 x2 Label
addi x3 x0 1
addi x3 x0 2
addi x3 x0 3
addi x3 x0 4
addi x3 x0 5

Label:
addi x3 x0 100

li x1 35

beq x1 x2 Label2
addi x3 x0 0
Label2:
addi x3 x0 101