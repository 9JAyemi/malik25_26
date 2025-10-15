# test sw

li x2, 700
li x1, 123
outr x1  ; 123
; outr x2   ; 500
sw x1, 0(x2)   ; store 123 to addr 500
outloc 700   ; OUT 123

li x2, 800
li x1, 111
sw x1, 0(x2)
outloc 800    ; 111

outloc 700    ; 123
outloc 800    ; 111

# test non-zero offset to load and store

li x1, 111
sw x1, 600(x0)

li x1, 222
sw x1, 610(x0)

lw x3, 600(x0)
outr x3          ; OUT 111
lw x3, 610(x0)
outr x3          ; OUT 222

;=====================

li x2, 300    ; x2 = 300
; outr x2     ; OUT 300

li x3, 416    ; x3 = 416
; outr x3     ; OUT 416

li x1, 444
sw x1, 400(x2)  ; addr 500 <= 444

li x1, 555
sw x1, 410(x3)   ; addr 416+210 = 626  <= 555

lw x4, 400(x2)
outr x4          ; OUT 444 <= addr 200 + 300 = 500
lw x4, 410(x3)
outr x4          ;  OUT 555  <= addr 210 + 416 = 526

lw x4, 284(x3)  ; 
outr x4       ; OUT 444
lw x4, 526(x2)
outr x4       ; OUT 555

# test lw

li x1, 123
li x2, 500
sw x1, 200(x2)  ; 123 to addr 500

li x1, 222
li x2, 510
sw x1, 200(x2)   ; 222 to addr 510

li x2, 500
lw x3, 200(x2)
outr x3    ; OUT 123

li x2, 510
lw x3, 200(x2)
outr x3     ; OUT  222

# negative offsets for load and store

li x1, 111
sw x1, 700(x0)  ; 111 to addr 500

li x1, 222
sw x1, 800(x0)  ; 222 to addr 600

li x3, 800

lw x1, -100(x3)  ; addr 800 - 300 = 500
outr x1  ; OUT 111

lw x1, -000(x3)  ; addr 800 - 200 = 600
outr x1   ; OUT 222

li x1, 444
sw x1, -100(x3)   ; store 444 to 800 -300 = 500

li x1, 555
sw x1, -000(x3)    ; store 555 to 800 - 200 = 600

lw x1, 700(x0)    ; load from 500
outr x1   ; OUT 444

lw x1, 800(x0)    ; load from 600
outr x1    ; OUT 555

halt
