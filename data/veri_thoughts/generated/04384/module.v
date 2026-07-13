
module three_input_and_gate (
    X,
    A1,
    A2,
    A3
);

    output X;
    input A1;
    input A2;
    input A3;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

endmodule

module sky130_fd_sc_lp__a311o_0 (
    output X,
    input A1,
    input A2,
    input A3,
    input B1,
    input C1
);

    assign X = (A1 & A2 & A3 & B1 & C1);

endmodule
