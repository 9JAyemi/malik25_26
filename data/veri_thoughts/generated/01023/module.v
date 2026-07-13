
module sky130_fd_sc_lp__cap_1 (
    input A,
    output P,
    input n,
    input C
);

    assign P = A & ~n;

endmodule
