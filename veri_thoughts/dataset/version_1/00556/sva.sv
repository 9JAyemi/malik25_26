module my_module_sva (
    input logic Z,
    input logic A,
    input logic TE_B
);

    // Z always matches the RTL mux equation.
    check_z_matches_mux_equation: assert property (
        @($global_clock) Z == (TE_B ? 1'b1 : A)
    );

    // TE_B high forces Z high.
    check_te_b_high_forces_z_high: assert property (
        @($global_clock) TE_B |-> (Z == 1'b1)
    );

    // TE_B low makes Z follow A.
    check_te_b_low_passes_a: assert property (
        @($global_clock) !TE_B |-> (Z == A)
    );

    // Z low can only occur when both TE_B and A are low.
    check_z_low_requires_te_b_low_and_a_low: assert property (
        @($global_clock) !Z |-> (!TE_B && !A)
    );

endmodule