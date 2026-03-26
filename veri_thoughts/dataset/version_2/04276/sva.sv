module sky130_fd_sc_lp__o32a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic clk
);

    // X matches the implemented OR-AND function.
    check_output_equation: assert property (
        @(posedge clk) X == ((A1 | A2 | A3) & (B1 | B2))
    );

    // If all A inputs are low, X must be low.
    check_a_group_zero_forces_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b0)
    );

    // If all B inputs are low, X must be low.
    check_b_group_zero_forces_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // If both OR groups are active, X must be high.
    check_both_groups_active_drive_high: assert property (
        @(posedge clk) (((A1 | A2 | A3) == 1'b1) && ((B1 | B2) == 1'b1)) |-> (X == 1'b1)
    );

    // A1 alone can satisfy the A-side OR when the B-side OR is high.
    check_a1_singleton_enables_output: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b0) && ((B1 | B2) == 1'b1)) |-> (X == 1'b1)
    );

    // A2 alone can satisfy the A-side OR when the B-side OR is high.
    check_a2_singleton_enables_output: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b1) && (A3 == 1'b0) && ((B1 | B2) == 1'b1)) |-> (X == 1'b1)
    );

    // A3 alone can satisfy the A-side OR when the B-side OR is high.
    check_a3_singleton_enables_output: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b1) && ((B1 | B2) == 1'b1)) |-> (X == 1'b1)
    );

    // B1 alone can satisfy the B-side OR when the A-side OR is high.
    check_b1_singleton_enables_output: assert property (
        @(posedge clk) (((A1 | A2 | A3) == 1'b1) && (B1 == 1'b1) && (B2 == 1'b0)) |-> (X == 1'b1)
    );

    // B2 alone can satisfy the B-side OR when the A-side OR is high.
    check_b2_singleton_enables_output: assert property (
        @(posedge clk) (((A1 | A2 | A3) == 1'b1) && (B1 == 1'b0) && (B2 == 1'b1)) |-> (X == 1'b1)
    );

endmodule