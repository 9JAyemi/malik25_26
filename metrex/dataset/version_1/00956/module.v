module sky130_fd_sc_ls__or4b (
    input  A   ,
    input  B   ,
    input  C   ,
    input  D_N ,
    output X   ,

    input  VPB ,
    input  VPWR,
    input  VGND,
    input  VNB
);

wire AB, CD_N, ABCD_N;
assign AB = A | B;
assign CD_N = C | D_N;
assign ABCD_N = AB | CD_N;
assign X = ~ABCD_N;

endmodule