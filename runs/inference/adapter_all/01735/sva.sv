module tri_buf_sva (
    input logic clk,
    input logic A,
    input logic Z,
    input logic TE_B
);

    // Z must always match the tri-state function.
    check_z_matches_function: assert property (
        @(posedge clk) Z == (TE_B ? 1'b0 : A)
    );

    // When tri-state is enabled, Z must be forced low.
    check_z_low_when_tri_state_enabled: assert property (
        @(posedge clk) TE_B |-> (Z == 1'b0)
    );

    // When tri-state is disabled, Z must follow A.
    check_z_follows_a_when_enabled: assert property (
        @(posedge clk) !TE_B |-> (Z == A)
    );

    // A low must appear on Z when enabled.
    check_a_low_appears_on_z: assert property (
        @(posedge clk) (!TE_B && !A) |-> (Z == 1'b0)
    );

    // A high must appear on Z when enabled.
    check_a_high_appears_on_z: assert property (
        @(posedge clk) (!TE_B && A) |-> (Z == 1'b1)
    );

endmodule