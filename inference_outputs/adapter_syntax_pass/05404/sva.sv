module sky130_fd_sc_hvl__a22oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND/AND/buffer function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ((~(A1 & A2)) & (~(B1 & B2)))
    );

    // A1 and A2 high forces Y low.
    check_a_pair_high_forces_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // B1 and B2 high forces Y low.
    check_b_pair_high_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // With both input pairs inactive, Y is high.
    check_both_pairs_inactive_drive_y_high: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> Y
    );

    // A high Y means neither input pair is fully high.
    check_y_high_implies_no_active_pair: assert property (
        @(posedge clk) Y |-> (!(A1 & A2) && !(B1 & B2))
    );

endmodule