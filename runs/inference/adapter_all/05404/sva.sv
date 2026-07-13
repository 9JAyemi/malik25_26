module sky130_fd_sc_hvl__a22oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((~(A2 & A1)) & (~(B2 & B1)))
    );

    // Both A inputs high force Y low.
    check_a_pair_high_forces_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // Both B inputs high force Y low.
    check_b_pair_high_forces_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // With both input pairs inactive, Y is high.
    check_both_pairs_inactive_drive_high: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> Y
    );

    // With only the A pair inactive, Y is high.
    check_only_a_pair_inactive_drive_high: assert property (
        @(posedge clk) (!(A1 & A2) && (B1 & B2)) |-> Y
    );

    // With only the B pair inactive, Y is high.
    check_only_b_pair_inactive_drive_high: assert property (
        @(posedge clk) ((A1 & A2) && !(B1 & B2)) |-> Y
    );

    // A low Y requires at least one input pair to be high.
    check_low_output_has_active_pair: assert property (
        @(posedge clk) !Y |-> ((A1 & A2) || (B1 & B2))
    );

endmodule