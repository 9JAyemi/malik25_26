module sky130_fd_sc_hvl__o22a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic or0_out,
    input logic or1_out,
    input logic and0_out_X
);
    // or0_out implements A1 OR A2.
    check_or0_definition: assert property (
        @(posedge clk) or0_out == (A1 | A2)
    );

    // or1_out implements B1 OR B2.
    check_or1_definition: assert property (
        @(posedge clk) or1_out == (B1 | B2)
    );

    // and0_out_X implements or0_out AND or1_out.
    check_and0_definition: assert property (
        @(posedge clk) and0_out_X == (or0_out & or1_out)
    );

    // X buffers and0_out_X.
    check_buf_definition: assert property (
        @(posedge clk) X == and0_out_X
    );

    // X equals (A1 OR A2) AND (B1 OR B2).
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 | A2) & (B1 | B2))
    );

    // If both A1 and A2 are LOW, X must be LOW.
    check_A_group_zero_forces_X_zero: assert property (
        @(posedge clk) (~A1 & ~A2) |-> (X == 1'b0)
    );

    // If both B1 and B2 are LOW, X must be LOW.
    check_B_group_zero_forces_X_zero: assert property (
        @(posedge clk) (~B1 & ~B2) |-> (X == 1'b0)
    );

    // If X is HIGH, at least one of A1/A2 is HIGH.
    check_X_high_implies_A_group_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (A1 | A2)
    );

    // If X is HIGH, at least one of B1/B2 is HIGH.
    check_X_high_implies_B_group_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (B1 | B2)
    );

    // If A1 and B1 are HIGH, X must be HIGH.
    check_A1_and_B1_suffices_for_X_high: assert property (
        @(posedge clk) (A1 & B1) |-> (X == 1'b1)
    );
endmodule