module sky130_fd_sc_lp__nor2 (
    Y,
    A,
    B
);

    output Y;
    input  A;
    input  B;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // NOR gate implementation
    assign Y = ~(A | B);

endmodule