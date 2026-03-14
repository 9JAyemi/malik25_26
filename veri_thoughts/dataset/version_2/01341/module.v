
module sky130_fd_sc_hs__a2bb2o (
    input  A1_N,
    input  A2_N,
    input  B1  ,
    input  B2  ,
    output X
);

    supply1 VPWR;
    supply0 VGND;

    // module logic goes here
    assign X = (B2 || A2_N) && (B1 || A1_N);

endmodule