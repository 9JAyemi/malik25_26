
module sky130_fd_sc_lp__udp_mux2_1_N (
    Y,
    A,
    B,
    S
);

    // Module ports
    output Y;
    input A;
    input B;
    input S;

    // Implement the 2-to-1 multiplexer using logic gates
    assign Y = (S) ? B : A;

endmodule

module mux2i (
    Y,
    A0,
    A1,
    S
);

    // Module ports
    output Y;
    input A0;
    input A1;
    input S;

    // Instantiate the two-to-one multiplexer
    sky130_fd_sc_lp__udp_mux2_1_N mux_2to1 (
        .Y(Y),
        .A(A0),
        .B(A1),
        .S(S)
    );

endmodule
