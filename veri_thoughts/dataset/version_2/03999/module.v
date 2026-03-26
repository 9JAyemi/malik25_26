module sky130_fd_sc_ls__nor2_1 (
    output Y,
    input A,
    input B
);

    sky130_fd_sc_ls__nor2 base (
        .Y(Y),
        .A(A),
        .B(B)
    );

endmodule

module sky130_fd_sc_ls__nor2 (
    output Y,
    input A,
    input B
);

    assign Y = ~(A | B);

endmodule