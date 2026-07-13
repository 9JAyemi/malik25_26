module sky130_fd_sc_hd__o41ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // Y implements the O41AI Boolean equation.
    check_y_matches_o41ai_equation: assert property (
        @($global_clock) Y == ~(B1 & (A1 | A2 | A3 | A4))
    );

    // B1 low forces Y high.
    check_y_high_when_b1_low: assert property (
        @($global_clock) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // All A inputs low force Y high.
    check_y_high_when_all_a_low: assert property (
        @($global_clock) ((A1 | A2 | A3 | A4) == 1'b0) |-> (Y == 1'b1)
    );

    // B1 and A1 high force Y low.
    check_y_low_when_b1_a1_high: assert property (
        @($global_clock) ((B1 == 1'b1) && (A1 == 1'b1)) |-> (Y == 1'b0)
    );

    // B1 and A2 high force Y low.
    check_y_low_when_b1_a2_high: assert property (
        @($global_clock) ((B1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // B1 and A3 high force Y low.
    check_y_low_when_b1_a3_high: assert property (
        @($global_clock) ((B1 == 1'b1) && (A3 == 1'b1)) |-> (Y == 1'b0)
    );

    // B1 and A4 high force Y low.
    check_y_low_when_b1_a4_high: assert property (
        @($global_clock) ((B1 == 1'b1) && (A4 == 1'b1)) |-> (Y == 1'b0)
    );

endmodule