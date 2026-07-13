module sky130_fd_sc_lp__a221oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y matches the implemented NOR of C1 and the two AND terms.
    check_y_matches_logic: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high forces the output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> (Y == 1'b0)
    );

    // A1 and A2 high force the output low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> (Y == 1'b0)
    );

    // B1 and B2 high force the output low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> (Y == 1'b0)
    );

    // With all NOR inputs inactive, the output is high.
    check_all_terms_inactive_drive_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // A high output implies none of the three NOR inputs is active.
    check_y_high_implies_all_terms_inactive: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

endmodule