module or3_module (
    input  A   ,
    input  B   ,
    input  C   ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB ,
    output X   
);

    //sky130_fd_sc_lp__or3 base (
    //    .X(X),
    //    .A(A),
    //    .B(B),
    //    .C(C),
    //    .VPWR(VPWR),
    //    .VGND(VGND),
    //    .VPB(VPB),
    //    .VNB(VNB)
    //);

    // Define your OR3 gate here
    assign X = A | B | C;

endmodule 