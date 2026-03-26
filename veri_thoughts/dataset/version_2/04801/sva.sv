module sky130_fd_sc_hdll__a21oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y implements the inverted OR of B1 and A1&A2.
    check_y_matches_a21oi_function: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1)
    );

    // B1 high forces the NOR output low.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // A1 and A2 high force the AND term high and drive Y low.
    check_a1a2_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1 low and A1 low, the AND term is low and Y is high.
    check_b1_low_a1_low_gives_y_high: assert property (
        @(posedge clk) (!B1 && !A1) |-> Y
    );

    // With B1 low and A2 low, the AND term is low and Y is high.
    check_b1_low_a2_low_gives_y_high: assert property (
        @(posedge clk) (!B1 && !A2) |-> Y
    );

    // Y high only when B1 is low and the A1&A2 term is low.
    check_y_high_only_for_valid_inputs: assert property (
        @(posedge clk) Y |-> (!B1 && !(A1 && A2))
    );

    // Y low only when B1 is high or the A1&A2 term is high.
    check_y_low_only_for_valid_inputs: assert property (
        @(posedge clk) !Y |-> (B1 || (A1 && A2))
    );

endmodule