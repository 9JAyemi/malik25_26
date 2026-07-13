module my_buffer_sva (
    input logic A,
    input logic Z,
    input logic TE_B,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Z must always match the RTL mux expression.
    check_output_matches_mux_expression: assert property (
        @($global_clock) Z == (TE_B ? A : 1'b0)
    );

    // When TE_B is low, Z must be forced low.
    check_te_b_low_forces_z_low: assert property (
        @($global_clock) !TE_B |-> !Z
    );

    // When TE_B is high, Z must follow A.
    check_te_b_high_passes_a: assert property (
        @($global_clock) TE_B |-> (Z == A)
    );

endmodule