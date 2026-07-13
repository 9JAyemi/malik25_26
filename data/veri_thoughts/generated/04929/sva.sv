module sky130_fd_sc_ms__o22a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must match the OR-OR-AND function every cycle.
    check_x_matches_function: assert property (
        @(posedge clk) disable iff (1'b0)
        X == ((A1 | A2) & (B1 | B2))
    );

    // A high X requires at least one A-side input to be high.
    check_x_high_requires_a_side: assert property (
        @(posedge clk) disable iff (1'b0)
        X |-> (A1 | A2)
    );

    // A high X requires at least one B-side input to be high.
    check_x_high_requires_b_side: assert property (
        @(posedge clk) disable iff (1'b0)
        X |-> (B1 | B2)
    );

    // If both A-side inputs are low, X must be low.
    check_no_a_side_forces_x_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!(A1 | A2)) |-> (!X)
    );

    // If both B-side inputs are low, X must be low.
    check_no_b_side_forces_x_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!(B1 | B2)) |-> (!X)
    );

    // A1 with B1 high must drive X high.
    check_a1_b1_drive_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & B1) |-> X
    );

    // A1 with B2 high must drive X high.
    check_a1_b2_drive_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & B2) |-> X
    );

    // A2 with B1 high must drive X high.
    check_a2_b1_drive_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A2 & B1) |-> X
    );

    // A2 with B2 high must drive X high.
    check_a2_b2_drive_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A2 & B2) |-> X
    );

endmodule