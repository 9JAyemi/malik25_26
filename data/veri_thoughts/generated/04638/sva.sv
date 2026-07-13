module sky130_fd_sc_hd__o31a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X must match the implemented OR-then-AND function.
    check_x_matches_function: assert property (
        @(posedge clk) X == (B1 & (A1 | A2 | A3))
    );

    // B1 low must force the output low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // All A inputs low must force the output low.
    check_all_a_low_forces_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b0)
    );

    // With B1 high and any A input high, the output must be high.
    check_or_term_with_b1_drives_x_high: assert property (
        @(posedge clk) ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))) |-> (X == 1'b1)
    );

    // A high output requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (B1 == 1'b1)
    );

    // A high output requires at least one A input to be high.
    check_x_high_requires_any_a_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))
    );

    // If B1 is high and X is low, all A inputs must be low.
    check_x_low_with_b1_high_requires_all_a_low: assert property (
        @(posedge clk) ((B1 == 1'b1) && (X == 1'b0)) |-> ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0))
    );

endmodule