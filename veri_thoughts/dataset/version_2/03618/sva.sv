module sky130_fd_sc_ms__a221oi_sva (
    (* gclk *) input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y must match the implemented A221OI boolean function.
    check_y_matches_boolean_function: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        C1 |-> !Y
    );

    // A1 and A2 high together force Y low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & A2) |-> !Y
    );

    // B1 and B2 high together force Y low.
    check_b1_b2_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 & B2) |-> !Y
    );

    // If all three NOR inputs are inactive, Y must be high.
    check_all_terms_inactive_give_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (!C1 && !(A1 & A2) && !(B1 & B2)) |-> Y
    );

    // Y high implies none of the three NOR inputs are active.
    check_y_high_implies_all_terms_inactive: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

    // Y low implies at least one NOR input is active.
    check_y_low_implies_some_term_active: assert property (
        @(posedge clk) disable iff (1'b0)
        !Y |-> (C1 || (A1 & A2) || (B1 & B2))
    );

endmodule