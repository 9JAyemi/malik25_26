module sky130_fd_sc_lp__a31o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X matches the implemented AO31 logic function.
    check_output_matches_a31o: assert property (
        @(posedge clk) disable iff (1'b0) X == ((A1 & A2 & A3) | B1)
    );

    // B1 high forces the OR output high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0) B1 |-> X
    );

    // A1, A2, and A3 high force the AND term high.
    check_and_term_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0) (A1 & A2 & A3) |-> X
    );

    // With B1 low, X follows the three-input AND term.
    check_b1_low_makes_x_follow_and_term: assert property (
        @(posedge clk) disable iff (1'b0) !B1 |-> (X == (A1 & A2 & A3))
    );

    // If neither term is active, X must be low.
    check_no_active_term_keeps_x_low: assert property (
        @(posedge clk) disable iff (1'b0) (!B1 && !(A1 & A2 & A3)) |-> !X
    );

    // X low implies the B1 OR input is low.
    check_x_low_requires_b1_low: assert property (
        @(posedge clk) disable iff (1'b0) !X |-> !B1
    );

    // X low implies the three-input AND term is low.
    check_x_low_requires_and_term_low: assert property (
        @(posedge clk) disable iff (1'b0) !X |-> !(A1 & A2 & A3)
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_keep_x_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable({A1, A2, A3, B1}) |-> $stable(X)
    );

endmodule