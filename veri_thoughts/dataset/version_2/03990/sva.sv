module sky130_fd_sc_ls__or2b_sva (
    input logic clk,
    input logic A,
    input logic B_N,
    input logic X
);

    // X must match the implemented NAND of A and B_N.
    check_nand_function: assert property (
        @(posedge clk) X == ~(A & B_N)
    );

    // A low forces X high.
    check_a_low_forces_x_high: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b1)
    );

    // B_N low forces X high.
    check_bn_low_forces_x_high: assert property (
        @(posedge clk) (B_N == 1'b0) |-> (X == 1'b1)
    );

    // Both inputs high force X low.
    check_both_high_drive_x_low: assert property (
        @(posedge clk) ((A == 1'b1) && (B_N == 1'b1)) |-> (X == 1'b0)
    );

endmodule