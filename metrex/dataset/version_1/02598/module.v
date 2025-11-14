module mux_2to1 (
    input A,
    input B,
    input SEL,
    output Y,
    input VPWR,
    input VGND
);

    wire not_sel;
    wire and1_out;
    wire and2_out;

    sky130_fd_sc_lp__not_1 not_gate_inst(
        .A(SEL),
        .X(not_sel),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    sky130_fd_sc_lp__and2_1 and1_gate_inst(
        .A(A),
        .B(not_sel),
        .X(and1_out),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    sky130_fd_sc_lp__and2_1 and2_gate_inst(
        .A(B),
        .B(SEL),
        .X(and2_out),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    assign Y = and1_out | and2_out;

endmodule

module sky130_fd_sc_lp__not_1 (
    input A,
    output X,
    input VPWR,
    input VGND
);

    assign X = ~A;

endmodule

module sky130_fd_sc_lp__and2_1 (
    input A,
    input B,
    output X,
    input VPWR,
    input VGND
);

    assign X = A & B;

endmodule