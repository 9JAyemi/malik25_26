module sky130_fd_sc_hdll__o22a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X matches the implemented OR-OR-AND function.
    check_o22a_equation: assert property (
        @(posedge clk) X == ((A1 | A2) & (B1 | B2))
    );

    // Both A-side inputs low force X low.
    check_a_side_low_forces_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // Both B-side inputs low force X low.
    check_b_side_low_forces_x_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // Any high on both sides drives X high.
    check_any_a_and_any_b_drive_x_high: assert property (
        @(posedge clk) (((A1 | A2) & (B1 | B2)) == 1'b1) |-> (X == 1'b1)
    );

    // X high requires at least one A-side input high.
    check_x_high_requires_a_side_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 | A2) == 1'b1)
    );

    // X high requires at least one B-side input high.
    check_x_high_requires_b_side_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((B1 | B2) == 1'b1)
    );

endmodule