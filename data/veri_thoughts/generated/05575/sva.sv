module sky130_fd_sc_ms__a2111oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y matches the implemented AOI function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1 | C1 | D1)
    );

    // B1 high forces the output low.
    check_b1_forces_output_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // C1 high forces the output low.
    check_c1_forces_output_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // D1 high forces the output low.
    check_d1_forces_output_low: assert property (
        @(posedge clk) D1 |-> !Y
    );

    // A1 and A2 high together force the output low.
    check_and_term_forces_output_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1, C1, and D1 low, A1 low keeps the output high.
    check_a1_low_keeps_output_high: assert property (
        @(posedge clk) (!B1 && !C1 && !D1 && !A1) |-> Y
    );

    // With B1, C1, and D1 low, A2 low keeps the output high.
    check_a2_low_keeps_output_high: assert property (
        @(posedge clk) (!B1 && !C1 && !D1 && !A2) |-> Y
    );

    // A high output requires all NOR inputs low and the AND term inactive.
    check_output_high_requires_all_inputs_clear: assert property (
        @(posedge clk) Y |-> (!B1 && !C1 && !D1 && !(A1 && A2))
    );

    // A low output must be caused by a high NOR input or the AND term.
    check_output_low_has_active_input: assert property (
        @(posedge clk) !Y |-> (B1 || C1 || D1 || (A1 && A2))
    );

endmodule