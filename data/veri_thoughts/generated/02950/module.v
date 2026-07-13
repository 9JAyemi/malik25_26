module sky130_fd_sc_hs__nor4b (
    input  A   ,
    input  B   ,
    input  C   ,
    input  D_N ,
    output Y   ,
    input  VPWR,
    input  VGND
);

assign Y = ~(A | B | C | D_N);

endmodule