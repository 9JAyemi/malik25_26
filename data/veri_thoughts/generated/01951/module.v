module sky130_fd_sc_lp__a2111o_2 (
    output X ,
    input  A1,
    input  A2,
    input  B1,
    input  C1,
    input  D1
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and1, and2, and3;

    assign and1 = A1 & A2;
    assign and2 = B1 & C1 & D1;
    assign X = and1 | and2;

endmodule

module and_gate (
    output Z,
    input A,
    input B
);
    assign Z = A & B;
endmodule

module or_gate (
    output Z,
    input A,
    input B
);
    assign Z = A | B;
endmodule