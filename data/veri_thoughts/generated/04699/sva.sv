module sky130_fd_sc_hs__o2bb2a_sva (
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Combinational cell with no RTL clock or reset; sample on the formal global clock.

    // X must always match the implemented combinational equation.
    check_x_matches_rtl_function: assert property (
        @($global_clock) disable iff (1'b0)
        X == ((~A1_N & B1 & B2) | (~A2_N & (B1 | B2)))
    );

    // If both active-low A inputs are deasserted, X must be low.
    check_both_a_inputs_deasserted_force_low: assert property (
        @($global_clock) disable iff (1'b0)
        (A1_N && A2_N) |-> (!X)
    );

    // If both B inputs are low, neither product term can assert X.
    check_both_b_inputs_low_force_low: assert property (
        @($global_clock) disable iff (1'b0)
        ((!B1) && (!B2)) |-> (!X)
    );

    // With only the A1 path enabled, X reduces to B1 & B2.
    check_a1_only_path_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        ((!A1_N) && A2_N) |-> (X == (B1 & B2))
    );

    // With only the A2 path enabled, X reduces to B1 | B2.
    check_a2_only_path_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        (A1_N && (!A2_N)) |-> (X == (B1 | B2))
    );

    // With both paths enabled, X still reduces to B1 | B2.
    check_both_paths_enabled_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        ((!A1_N) && (!A2_N)) |-> (X == (B1 | B2))
    );

    // If both B inputs are high, X depends only on whether either A path is enabled.
    check_both_b_inputs_high_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        (B1 && B2) |-> (X == ((~A1_N) | (~A2_N)))
    );

    // Enabling the A2 term with either B input high must assert X.
    check_a2_term_asserts_x: assert property (
        @($global_clock) disable iff (1'b0)
        ((!A2_N) && (B1 || B2)) |-> X
    );

    // Enabling the A1 term with both B inputs high must assert X.
    check_a1_term_asserts_x: assert property (
        @($global_clock) disable iff (1'b0)
        ((!A1_N) && B1 && B2) |-> X
    );

endmodule