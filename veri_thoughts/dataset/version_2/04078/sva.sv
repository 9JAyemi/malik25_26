module MX2X4A12TR_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S0,
    input logic Y
);

    // RTL has no native clock or reset; clk is used only for assertion sampling.
    // The logic is purely combinational and implements Y = S0 ? (A & ~B) : (A & B).

    // Y must always match the muxed AND function implemented in the RTL.
    check_mux_function_exact: assert property (
        @(posedge clk) Y == (S0 ? (A & ~B) : (A & B))
    );

    // When S0 is low, Y must select the A & B path.
    check_select_low_path: assert property (
        @(posedge clk) !S0 |-> (Y == (A & B))
    );

    // When S0 is high, Y must select the A & ~B path.
    check_select_high_path: assert property (
        @(posedge clk) S0 |-> (Y == (A & ~B))
    );

    // If A is low, both product terms are low and Y must be low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // A high Y requires A high and the selected B polarity to be true.
    check_y_high_requires_active_path: assert property (
        @(posedge clk) Y |-> (A && (S0 ? ~B : B))
    );

    // If B matches S0, neither selected product term can drive Y high.
    check_b_matches_select_forces_y_low: assert property (
        @(posedge clk) !(B ^ S0) |-> !Y
    );

endmodule