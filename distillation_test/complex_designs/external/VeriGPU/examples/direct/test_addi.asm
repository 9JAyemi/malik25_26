# test addi

addi x1, x0, 22
outr x1

addi x3, x0, 1000
outr x3

addi x5, x0, 1234
outr x5

outr x3
outr x5

# negative immediate for addi

li x1, 123
outr x1

addi x3, x1, 2
outr x3

addi x3, x1, -1
outr x3

addi x3, x1, -10
outr x3

addi x3, x1, -100
outr x3

addi x3, x0, -1000
outr x3

addi x3, x0, -2000
outr x3

addi x3, x0, 2000
outr x3

halt
