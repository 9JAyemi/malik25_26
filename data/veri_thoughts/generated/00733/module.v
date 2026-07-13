
module or4_module (
    input A,
    input B,
    input C_N,
    input D_N,
    output X
);

    wire or_out;

    sky130_fd_sc_hdll__or4bb_2 or_inst (
        .X(or_out),
        .A(A),
        .B(B),
        .C_N(C_N),
        .D_N(D_N)
    );

    assign X = or_out;

endmodule
module sky130_fd_sc_hdll__or4bb_2 (
    output X,
    input A,
    input B,
    input C_N,
    input D_N
);

    assign X = A | B | ~C_N | ~D_N;

endmodule