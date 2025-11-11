
module sky130_fd_sc_hs__dlymetal6s2s (
    input A,
    input D,
    input delay_VPWR,
    input delay_VGND,
    output reg X
);

reg delay_A; // register to delay A by 1
reg delay_D; // register to delay D by 1

// Delay A by 1
always @(posedge A)
    delay_A <= A;

// Delay D by 1
always @(posedge D)
    delay_D <= D;

// Output X when delayed A, delay_VPWR, delay_VGND, and D are all high
always @*
    X <= delay_A && delay_VPWR && delay_VGND && delay_D;

endmodule