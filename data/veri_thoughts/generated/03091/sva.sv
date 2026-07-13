module sky130_fd_sc_ms__o2bb2ai_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Purely combinational DUT with no RTL clock or reset; sample on $global_clock.

    // Y matches the implemented NAND/OR/NAND gate equation.
    check_output_equation: assert property (
        @($global_clock) Y == ~(~(A2_N & A1_N) & (B2 | B1))
    );

    // Both A inputs high force the final output high.
    check_force_high_from_a_inputs: assert property (
        @($global_clock) (A1_N & A2_N) |-> Y
    );

    // Both B inputs low force the final output high.
    check_force_high_from_b_inputs: assert property (
        @($global_clock) ~(B1 | B2) |-> Y
    );

    // Any high B input with at least one low A input forces Y low.
    check_force_low_when_b_high_and_a_not_both_high: assert property (
        @($global_clock) (~(A1_N & A2_N) & (B1 | B2)) |-> ~Y
    );

    // A low output can only occur in the single low-producing input condition.
    check_low_output_only_for_low_condition: assert property (
        @($global_clock) ~Y |-> (~(A1_N & A2_N) & (B1 | B2))
    );

    // A high output must come from both A inputs high or both B inputs low.
    check_high_output_condition: assert property (
        @($global_clock) Y |-> ((A1_N & A2_N) | (~B1 & ~B2))
    );

endmodule